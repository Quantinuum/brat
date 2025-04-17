module Brat.Checker.Monad where

import Brat.Checker.Quantity (Quantity(..))
import Brat.Checker.Types hiding (HoleData(..))
import Brat.Constructors (ConstructorMap, CtorArgs)
import Brat.Error (Error(..), ErrorMsg(..), dumbErr)
import Brat.FC (FC)
import Brat.Graph
import Brat.Naming (fresh, split, Name, Namespace, FreshMonad(..))
import Brat.QualName (QualName)
import Brat.Syntax.Common
import Brat.Syntax.Value
import Hasochism
import Util

import Control.Monad.Freer

import Control.Monad.Fail ()
import Data.List (intercalate)
import qualified Data.Map as M

-- import Debug.Trace

trackM :: Monad m => String -> m ()
trackM = const (pure ())
-- trackM = traceM

track = const id
-- track = trace
trackShowId x = track (show x) x

-- Data for using a type alias. E.g.
-- type A(x :: *, y :: #, z :: *(a :: *)) = body (with [x,y,z] in scope)
-- this gets encoded as VLam (VLam (VLam body))
type Alias = ([(PortName, TypeKind)] -- The arguments to A, e.g. [("x", Star []),...] (allowed to be empty)
             ,Val Z -- The alias, rendered as i lambda abstractions over the body
             )

kindArgRows :: Stack Z (PortName, TypeKind) i -> (Ro Brat Z i, Ro Brat i (S i))
kindArgRows argKinds = (helper argKinds R0
                    ,REx ("type", Star []) R0
                    )
 where
  helper :: forall i j. Stack Z (PortName, TypeKind) i -> Ro Brat i j -> Ro Brat Z j
  helper S0 ro = ro
  helper (zx :<< (p,k)) ro = helper zx (REx (p,k) ro)

data CtxEnv = CtxEnv
  { globals :: VEnv
  , locals :: VEnv
  }

type Hopes = M.Map InPort FC

data Context = Ctx { globalVEnv :: VEnv
                   , store :: Store
                   , constructors :: ConstructorMap Brat
                   , kconstructors :: ConstructorMap Kernel
                   , typeConstructors :: M.Map (Mode, QualName) [(PortName, TypeKind)]
                   , aliasTable :: M.Map QualName Alias
                   , hopes :: Hopes
                   }

data CheckingSig ty where
  Fresh   :: String -> CheckingSig Name
  SplitNS :: String -> CheckingSig Namespace
  Throw   :: Error  -> CheckingSig a
  LogHole :: TypedHole -> CheckingSig ()
  AskFC   :: CheckingSig FC
  VLup    :: QualName -> CheckingSig (Maybe [(Src, BinderType Brat)])
  KLup    :: QualName -> CheckingSig (Maybe (Src, BinderType Kernel))
  -- Lookup type constructors
  TLup    :: (Mode, QualName) -> CheckingSig (Maybe [(PortName, TypeKind)])
  -- Lookup term constructor - ask whether a constructor builds a certain type
  CLup    :: FC -- File context for error reporting
          -> QualName -- Value constructor
          -> QualName  -- Type constructor
          -> CheckingSig (CtorArgs Brat)
  -- Lookup kernel constructors
  KCLup   :: FC -- File context for error reporting
          -> QualName -- Value constructor
          -> QualName  -- Type constructor
          -> CheckingSig (CtorArgs Kernel)
  -- Lookup an end in the Store
  ELup    :: End -> CheckingSig (Maybe (Val Z))
  -- Lookup an alias in the table
  ALup    :: QualName -> CheckingSig (Maybe Alias)
  TypeOf  :: End -> CheckingSig EndType
  AddNode :: Name -> Node -> CheckingSig ()
  Wire    :: Wire -> CheckingSig ()
  KDone   :: CheckingSig ()
  AskVEnv :: CheckingSig CtxEnv
  Declare :: End -> Modey m -> BinderType m -> Maybe String -> CheckingSig ()
  Define  :: End -> Val Z -> CheckingSig ()
  ANewHope :: InPort -> FC -> CheckingSig ()
  AskHopes :: CheckingSig Hopes
  RemoveHope :: InPort -> CheckingSig ()
  AskNames :: CheckingSig (M.Map End String)

localAlias :: (QualName, Alias) -> Checking v -> Checking v
localAlias _ (Ret v) = Ret v
localAlias con@(name, alias) (Req (ALup u) k)
  | u == name = localAlias con $ k (Just alias)
localAlias con (Req r k) = Req r (localAlias con . k)

localFC :: FC -> Checking v -> Checking v
localFC _ (Ret v) = Ret v
localFC f (Req AskFC k) = localFC f (k f)
localFC f (Req (Throw e@Err{fc=Nothing}) k) = localFC f (Req (Throw (e{fc=Just f})) k)
localFC f (Req r k) = Req r (localFC f . k)

localEnv :: (?my :: Modey m) => Env (EnvData m) -> Checking v -> Checking v
localEnv = case ?my of
  Braty -> localVEnv
  Kerny -> \env m -> localKVar env (m <* req KDone)

localVEnv :: VEnv -> Checking v -> Checking v
localVEnv _   (Ret v) = Ret v
localVEnv ext (Req (VLup x) k) | Just x <- M.lookup x ext = localVEnv ext (k (Just x))
localVEnv ext (Req AskVEnv k) = do env <- req AskVEnv
                                   -- ext shadows local vars
                                   localVEnv ext (k (env { locals = M.union ext (locals env) }))
localVEnv ext (Req r k) = Req r (localVEnv ext . k)

-- runs a computation, but intercepts uses of outer *locals* variables and redirects
-- them to use new outports of the specified node (expected to be a Source).
-- Returns a list of captured variables and their generated (Source-node) outports
captureOuterLocals :: Checking v -> Checking (v, VEnv)
captureOuterLocals c = do
  outerLocals <- locals <$> req AskVEnv
  helper (outerLocals, M.empty) c
 where
  helper :: (VEnv, VEnv) -> Checking v
         -> Checking (v, M.Map QualName [(Src, BinderType Brat)])
  helper (_, captured) (Ret v) = Ret (v, captured)
  helper (avail, captured) (Req (VLup x) k) | j@(Just new) <- M.lookup x avail =
    helper (avail, M.insert x new captured) (k j)
  helper state (Req r k) = Req r (helper state . k)

wrapError :: (Error -> Error) -> Checking v -> Checking v
wrapError _ (Ret v) = Ret v
wrapError f (Req (Throw e) k) = Req (Throw (f e)) k
wrapError f (Req r k) = Req r (wrapError f . k)

throwLeft :: Either ErrorMsg a -> Checking a
throwLeft (Right x) = pure x
throwLeft (Left msg) = err msg

vlup :: QualName -> Checking [(Src, BinderType Brat)]
vlup s = do
  req (VLup s) >>= \case
    Just vty -> pure vty
    Nothing -> err $ VarNotFound (show s)

alup :: QualName -> Checking Alias
alup s = do
  req (ALup s) >>= \case
    Just vty -> pure vty
    Nothing -> err $ VarNotFound (show s)

clup :: QualName -- Value constructor
     -> QualName  -- Type constructor
     -> Checking (CtorArgs Brat)
clup vcon tycon = req AskFC >>= \fc -> req (CLup fc vcon tycon)

kclup :: QualName -- Value constructor
      -> QualName  -- Type constructor
      -> Checking (CtorArgs Kernel)
kclup vcon tycon = req AskFC >>= \fc -> req (KCLup fc vcon tycon)

tlup :: (Mode, QualName) -> Checking [(PortName, TypeKind)]
tlup (m, c) = req (TLup (m, c)) >>= \case
  Nothing -> req (TLup (otherMode, c)) >>= \case
    Nothing -> err $ UnrecognisedTypeCon (show c)
    Just _ -> err $ WrongModeForType (show c)
  Just ks -> pure ks
 where
  otherMode = case m of
    Brat -> Kernel
    Kernel -> Brat

lookupAndUse :: QualName -> KEnv
             -> Either Error (Maybe ((Src, BinderType Kernel), KEnv))
lookupAndUse x kenv = case M.lookup x kenv of
   Nothing -> Right Nothing
   Just (None, _) -> Left $ dumbErr $ TypeErr $ show x ++ " has already been used"
   Just (One, rest)  -> Right $ Just (rest, M.insert x (None, rest) kenv)
   Just (Tons, rest) -> Right $ Just (rest, M.insert x (Tons, rest) kenv)

localKVar :: KEnv -> Checking v -> Checking v
localKVar _   (Ret v) = Ret v
localKVar env (Req (KLup x) k) = case lookupAndUse x env of
                                   Left err@(Err (Just _) _) -> req $ Throw err
                                   Left (Err Nothing msg) -> err msg
                                   Right (Just (th, env)) -> localKVar env (k (Just th))
                                   Right Nothing -> Req (KLup x) (localKVar env . k)
localKVar env (Req KDone k) = case [ x | (x,(One,_)) <- M.assocs env ] of
                                [] -> (localKVar env . k) ()
                                xs -> typeErr $
                                      unwords ["Variable(s)"
                                              ,intercalate ", " (fmap show xs)
                                              ,"haven't been used"
                                              ]
localKVar env (Req r k) = Req r (localKVar env . k)

catchErr :: Free CheckingSig a -> Free CheckingSig (Either Error a)
catchErr (Ret t) = Ret (Right t)
catchErr (Req (Throw e) _) = pure $ Left e
catchErr (Req r k) = Req r (catchErr . k)

handler :: Free CheckingSig v
        -> Context
        -> Graph
        -> Either Error (v,Context,([TypedHole],Graph))
handler (Ret v) ctx g = return (v, ctx, ([], g))
handler (Req s k) ctx g
  = case s of
      Fresh _ -> error "Fresh in handler, should only happen under `-!`"
      SplitNS _ -> error "SplitNS in handler, should only happen under `-!`"
      Throw err -> Left err
      LogHole hole -> do (v,ctx,(holes,g)) <- handler (k ()) ctx g
                         return (v,ctx,(hole:holes,g))
      AskFC -> error "AskFC in handler - shouldn't happen, should always be in localFC"
      VLup s -> handler (k $ M.lookup s (globalVEnv ctx)) ctx g
      ALup s -> handler (k $ M.lookup s (aliasTable ctx)) ctx g
      AddNode name node -> handler (k ()) ctx ((M.singleton name node, []) <> g)
      Wire w -> handler (k ()) ctx ((M.empty,[w]) <> g)
      -- We only get a KLup here if the variable has not been found in the kernel context
      KLup _ -> handler (k Nothing) ctx g
      -- Receiving KDone may become possible when merging the two check functions
      KDone -> error "KDone in handler - this shouldn't happen"
      AskVEnv -> handler (k (CtxEnv { globals = globalVEnv ctx, locals = M.empty })) ctx g
      ELup end -> handler (k (M.lookup end . valueMap . store $ ctx)) ctx g
      TypeOf end -> case M.lookup end . typeMap . store $ ctx of
        Just et -> handler (k et) ctx g
        Nothing -> Left (dumbErr . InternalError $ "End " ++ show end ++ " isn't Declared")
      Declare end my bty mname ->
        let st@Store{typeMap=typeMap,userNames=userNames} = store ctx
        in case M.lookup end typeMap of
          Just _ -> Left $ dumbErr (InternalError $ "Redeclaring " ++ show end)
          Nothing -> let bty_str = case my of { Braty -> show bty; Kerny -> show bty } in
                       track ("Declared " ++ show end ++ " :: " ++ bty_str) $
                       handler (k ())
                       (ctx { store =
                              st { typeMap = M.insert end (EndType my bty) typeMap
                                 , userNames = case mname of
                                    Just name -> M.insert end name userNames
                                    Nothing -> userNames
                                 }
                            }) g
      Define end v ->
        let st@Store{typeMap=tm, valueMap=vm} = store ctx
        in case track ("Define " ++ show end ++ " = " ++ show v) $ M.lookup end vm of
          Just _ -> Left $ dumbErr (InternalError $ "Redefining " ++ show end)
          Nothing -> case M.lookup end tm of
            Nothing -> Left $ dumbErr (InternalError $ "Defining un-Declared " ++ show end ++ " in \n" ++ show tm)
            Just _ -> -- TODO can we check the value is of the kind declared?
              handler (k ())
                (ctx { store =
                    st { valueMap = M.insert end v vm }
                }) g
      -- TODO: Use the kind argument for partially applied constructors
      TLup key -> do
        let args = M.lookup key (typeConstructors ctx)
        handler (k args) ctx g

      CLup fc vcon tycon -> do
        tbl <- maybeToRight (Err (Just fc) $ VConNotFound $ show vcon) $
               M.lookup vcon (constructors ctx)
        args <- maybeToRight (Err (Just fc) $ TyConNotFound (show tycon) (show vcon)) $
                M.lookup tycon tbl
        handler (k args) ctx g

      KCLup fc vcon tycon -> do
        tbl <- maybeToRight (Err (Just fc) $ VConNotFound $ show vcon) $
               M.lookup vcon (kconstructors ctx)
        args <- maybeToRight (Err (Just fc) $ TyConNotFound (show tycon) (show vcon)) $
                M.lookup tycon tbl
        handler (k args) ctx g

      ANewHope e fc -> handler (k ()) (ctx { hopes = M.insert e fc (hopes ctx) }) g

      AskHopes -> handler (k (hopes ctx)) ctx g

      RemoveHope e -> let hset = hopes ctx in
                        if M.member e hset
                        then handler (k ()) (ctx { hopes = M.delete e hset }) g
                        else Left (dumbErr (InternalError ("Trying to remove unknown Hope: " ++ show e)))
      AskNames -> handler (k (userNames (store ctx))) ctx g

type Checking = Free CheckingSig

instance Semigroup a => Semigroup (Checking a) where
  (<>) = liftA2 (<>)

instance Monoid a => Monoid (Checking a) where
  mempty = pure mempty
  mappend = liftA2 mappend

err :: ErrorMsg -> Checking a
err msg = do
  fc <- req AskFC
  req $ Throw $ Err (Just fc) msg

typeErr :: String -> Checking a
typeErr = err . TypeErr

instance FreshMonad Checking where
  freshName x = req $ Fresh x
  str -! c = inLvl str c

-- This way we get file contexts when pattern matching fails
instance MonadFail Checking where
  fail = typeErr

-- Run a computation without logging any holes
suppressHoles :: Checking a -> Checking a
suppressHoles (Ret x) = Ret x
suppressHoles (Req (LogHole _) k) = suppressHoles (k ())
suppressHoles (Req c k) = Req c (suppressHoles . k)

-- Run a computation without doing any graph generation
suppressGraph :: Checking a -> Checking a
suppressGraph (Ret x) = Ret x
suppressGraph (Req (AddNode _ _) k) = suppressGraph (k ())
suppressGraph (Req (Wire _) k) = suppressGraph (k ())
suppressGraph (Req c k) = Req c (suppressGraph . k)

inLvl :: String -> Checking a -> Checking a
inLvl prefix c = req (SplitNS prefix) >>= \prefixNamespace -> localNS prefixNamespace c

localNS :: Namespace -> Checking a -> Checking a
localNS _ (Ret v) = Ret v
localNS ns (Req (Fresh str) k) = let (name, root) = fresh str ns in
  localNS root (k name)
localNS ns (Req (SplitNS str) k) = let (subSpace, newRoot) = split str ns in
                                      localNS newRoot (k subSpace)
localNS ns (Req c k) = Req c (localNS ns . k)

defineEnd :: End -> Val Z -> Checking ()
defineEnd e v = req (Define e v)

showRowM :: ShowWithMetas ty => [(NamedPort e, ty)] -> Checking String
showRowM row = flip showRow row <$> req AskNames

showWithMetasM :: ShowWithMetas t => t -> Checking String
showWithMetasM x = flip showWithMetas x <$> req AskNames
