module Brat.Checker.Monad where

import Bwd
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
import Data.Functor ((<&>))
import Data.List (intercalate)
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace

-- Used for messages about thread forking / spawning
thTrace = const id
--thTrace = trace

trackM :: Monad m => String -> m ()
--trackM = const (pure ())
trackM = traceM

--track = const id
track = trace
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

data HopeData = HopeData
  { hopeFC :: Maybe FC
  , hopeDynamic :: Bool
  } deriving (Eq, Ord, Show)

type Hopes = M.Map InPort HopeData

type CaptureSets = M.Map Name VEnv

data Context = Ctx { globalVEnv :: VEnv
                   , store :: Store
                   , constructors :: ConstructorMap Brat
                   , kconstructors :: ConstructorMap Kernel
                   , typeConstructors :: M.Map (Mode, QualName) [(PortName, TypeKind)]
                   , aliasTable :: M.Map QualName Alias
                   -- On the chopping block
                   , hopes :: Hopes
                   -- Ends which need to be solved because they affect runtime behaviour
                   , dynamicSet :: M.Map End FC
                   , captureSets :: CaptureSets
                   }

mkFork :: String -> Free sig () -> Free sig ()
mkFork d par = thTrace ("Forking " ++ d) $ Fork d par $ pure ()

mkYield :: String -> S.Set End -> Free sig ()
mkYield desc es = thTrace ("Yielding in " ++ desc ++ "\n  " ++ show es) $ Yield (AwaitingAny es) (\_ -> trackM ("woke up " ++ desc) >> Ret ())

-- Commands for synchronous operations
data CheckingSig ty where
  Fresh   :: String -> CheckingSig Name
  SplitNS :: String -> CheckingSig Namespace
  AskNS   :: CheckingSig (Bwd (String, Int))
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
  TypeOf  :: End -> CheckingSig (EndType, IsSkolem)
  AddNode :: Name -> Node -> CheckingSig ()
  Wire    :: Wire -> CheckingSig ()
  KDone   :: CheckingSig ()
  AskVEnv :: CheckingSig CtxEnv
  Declare :: End -> Modey m -> BinderType m -> IsSkolem -> CheckingSig ()
  ANewDynamic :: End -> FC -> CheckingSig ()
  AskDynamics :: CheckingSig (M.Map End FC)
  AddCapture :: Name -> (QualName, [(Src, BinderType Brat)]) -> CheckingSig ()

wrapper :: (forall a. CheckingSig a -> Checking (Maybe a)) -> Checking v -> Checking v
wrapper _ (Ret v) = Ret v
wrapper f (Req s k) = f s >>= \case
  Just v -> wrapper f (k v)
  Nothing -> Req s (wrapper f . k)
wrapper f (Define lbl v e k) = Define lbl v e (wrapper f . k)
wrapper f (Yield st k) = Yield st (wrapper f . k)
wrapper f (Fork d par c) = Fork d (wrapper f par) (wrapper f c)

wrapper2 :: (forall a. CheckingSig a -> Maybe a) -> Checking v -> Checking v
wrapper2 f = wrapper (\s -> pure (f s))

localAlias :: (QualName, Alias) -> Checking v -> Checking v
localAlias (name, alias) = wrapper2 (\case
    ALup u | u == name -> Just (Just alias)
    _ -> Nothing)

localFC :: FC -> Checking v -> Checking v
localFC f = wrapper (\case
  AskFC -> pure $ Just f
  (Throw e@Err{fc=Nothing}) -> req (Throw (e{fc=Just f})) >> error "Throw returned"
  _ -> pure $ Nothing)

localEnv :: (?my :: Modey m) => Env (EnvData m) -> Checking v -> Checking v
localEnv = case ?my of
  Braty -> localVEnv
  Kerny -> \env m -> localKVar env (m <* req KDone)

localVEnv :: M.Map QualName [(Src, BinderType Brat)] -> Checking v -> Checking v
localVEnv ext = wrapper (\case
  (VLup x) | j@(Just _) <- M.lookup x ext -> pure $ Just j -- invoke continuation with j
  AskVEnv -> do
    outerEnv <- req AskVEnv
    pure $ Just -- value to return to original continuation
      (outerEnv { locals = M.union ext (locals outerEnv) })  -- ext shadows local vars
  _ -> pure Nothing)

-- runs a computation, but logs (via AddCapture, under the specified Name) uses of outer
-- *local* variables
captureOuterLocals :: Name -> Checking v -> Checking v
captureOuterLocals n c = do
  outerLocals <- locals <$> req AskVEnv
  wrapper (helper outerLocals) c
 where
  helper :: VEnv -> forall a. CheckingSig a -> Checking (Maybe a)
  helper avail (VLup x) | j@(Just new) <- M.lookup x avail =
    (req $ AddCapture n (x,new)) >> (pure $ Just j)
  helper _ _ = pure Nothing

wrapError :: (Error -> Error) -> Checking v -> Checking v
wrapError f = wrapper (\case
  (Throw e) -> req (Throw (f e)) -- do not return value from outer Throw!
  _ -> pure Nothing)

throwLeft :: Either ErrorMsg a -> Checking a
throwLeft (Right x) = pure x
throwLeft (Left msg) = err msg

vlup :: QualName -> Checking [(Src, BinderType Brat)]
vlup s = req (VLup s) >>= \case
    Just vty -> pure vty
    Nothing -> err $ VarNotFound (show s)

alup :: QualName -> Checking Alias
alup s = req (ALup s) >>= \case
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

-- TODO: Future proof this by taking a TypeKind argument instead of a mode.
-- Currently we have kinds `Nat` for `TypeFor m`, where we don't lookup `Nat`
-- with tlup, but this will change!
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
-- Doesn't fit the wrapper pattern because the `env` mutates
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
localKVar env (Define lbl e v k) = Define lbl e v (localKVar env . k)
localKVar env (Yield st k) = Yield st (localKVar env . k)
localKVar env (Fork desc par c) =
  -- can't send end both ways, so until we can join (TODO), restrict Forks to local scope
  thTrace ("Spawning(LKV) " ++ desc) $ localKVar env $ par *> c

-- SkolemConst constants are e.g. function parameters that are *not* going to be defined if we wait.
-- (exception: clause inputs can sometimes be defined if there is exactly one possible value).
isSkolem :: End -> Checking IsSkolem
isSkolem e = req (TypeOf e) <&> snd

catchErr :: Free CheckingSig a -> Free CheckingSig (Either Error a)
catchErr (Ret t) = Ret (Right t)
catchErr (Req (Throw e) _) = pure $ Left e
catchErr (Req r k) = Req r (catchErr . k)
catchErr (Define lbl e v k) = Define lbl e v (catchErr . k)
catchErr (Yield st k) = Yield st (catchErr . k)
catchErr (Fork desc par c) = thTrace ("Spawning(catch) " ++ desc) $ catchErr $ par *> c

handler :: Free CheckingSig v
        -> Context
        -> Graph
        -> Either Error (v,Context,([TypedHole],Graph))
handler (Ret v) ctx g = return (v, ctx, ([], g))
handler (Req s k) ctx g
  = case s of
      Fresh _ -> error "Fresh in handler, should only happen under `-!`"
      SplitNS _ -> error "SplitNS in handler, should only happen under `-!`"
      AskNS -> error "AskNS in handler, should only happen under `-!`"
      Throw err -> Left err
      LogHole hole -> do (v,ctx,(holes,g)) <- handler (k ()) ctx g
                         return (v,ctx,(hole:holes,g))
      AskFC -> error "AskFC in handler - shouldn't happen, should always be in localFC"
      VLup s -> handler (k $ M.lookup s (globalVEnv ctx)) ctx g
      ALup s -> handler (k $ M.lookup s (aliasTable ctx)) ctx g
      AddNode name node -> handler (k ()) ctx ((M.singleton name node, []) <> g)
      Wire w -> handler ((trace ("Wired: " ++ show w) k) ()) ctx ((M.empty,[w]) <> g)
      -- We only get a KLup here if the variable has not been found in the kernel context
      KLup _ -> handler (k Nothing) ctx g
      -- Receiving KDone may become possible when merging the two check functions
      KDone -> error "KDone in handler - this shouldn't happen"
      AskVEnv -> handler (k (CtxEnv { globals = globalVEnv ctx, locals = M.empty })) ctx g
      ELup end -> handler (k (M.lookup end . valueMap . store $ ctx)) ctx g
      TypeOf end -> case M.lookup end . typeMap . store $ ctx of
        Just et -> handler (k et) ctx g
        Nothing -> Left (dumbErr . InternalError $ "End " ++ show end ++ " isn't Declared")
      Declare end my bty skol ->
        let st@Store{typeMap=m} = store ctx
        in case M.lookup end m of
          Just _ -> Left $ dumbErr (InternalError $ "Redeclaring " ++ show end)
          Nothing -> let bty_str = case my of { Braty -> show bty; Kerny -> show bty } in
                       track ("Declared " ++ show end ++ " :: " ++ bty_str) $
                       handler (k ())
                       (ctx { store =
                              st { typeMap = M.insert end (EndType my bty, skol) m }
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

      ANewDynamic e fc -> trackM ("ANewDynamic " ++ show e) *> handler (k ()) (ctx { dynamicSet = M.insert e fc (dynamicSet ctx) }) g

      AskDynamics -> handler (k (dynamicSet ctx)) ctx g

      AddCapture n (var, ends) ->
        handler (k ()) ctx {captureSets=M.insertWith M.union n (M.singleton var ends) (captureSets ctx)} g

handler (Define lbl end v k) ctx g = let st@Store{typeMap=tm, valueMap=vm} = store ctx in
  case track ("Define(" ++ lbl ++ ")" ++ show end ++ " = " ++ show v) $ M.lookup end vm of
      Just _ -> Left $ dumbErr (InternalError $ "Redefining " ++ show end)
      Nothing -> case M.lookup end tm of
        Nothing -> Left $ dumbErr (InternalError $ "Defining un-Declared " ++ show end ++ " in \n" ++ show tm)
        -- Allow even Skolems to be defined (e.g. clauses with unique soln)
        -- TODO(1) can we check the value is of the kind declared?
        -- TODO(2) it'd be better to figure out if the end is really Unstuck,
        -- or just awaiting some other end, but that seems overly complex atm, as
        -- (a) we must be "Unstuck" if the end is Defined to something SkolemConst *OR* in the HopeSet,
        -- (b) Numbers are tricky, whether they are stuck or not depends upon the question
        -- (c) since there are no infinite end-creating loops, it's correct (merely inefficient)
        -- to just "have another go".
        Just _ -> let news = News (M.singleton end Unstuck)
                      newDynamics = (\x -> trace ("New dynamics: " ++ show x) x) $ case v of
                        VNum nv -> numVars nv
                        _ -> []
                  in handler (k news)
                     (ctx { store = st { valueMap = M.insert end v vm },
                                    dynamicSet = case M.lookup end (dynamicSet ctx) of
                                      Just fc -> track ("Replace " ++ show end ++ " with " ++ show newDynamics) $
                                                 M.union
                                                 (M.fromList (zip newDynamics (repeat fc)))
                                                 (M.delete end (dynamicSet ctx))
                                      Nothing -> dynamicSet ctx
                          }) g
handler (Yield Unstuck k) ctx g = handler (k mempty) ctx g
handler (Yield (AwaitingAny ends) _k) ctx _ = Left $ dumbErr $ TypeErr $ unlines $
  ("Typechecking blocked on:":(show <$> S.toList ends))
  ++ "":"Dynamic set is":(show <$> M.keys (dynamicSet ctx)) ++ ["Try writing more types! :-)"]
handler (Fork desc par c) ctx g = handler (thTrace ("Spawning " ++ desc) $ par *> c) ctx g

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
  whoAmI = req AskNS

-- This way we get file contexts when pattern matching fails
instance MonadFail Checking where
  fail = typeErr

-- Run a computation without logging any holes
suppressHoles :: Checking a -> Checking a
suppressHoles = wrapper2 (\case
  (LogHole _) -> Just ()
  _ -> Nothing)

-- Run a computation without doing any graph generation
suppressGraph :: Checking a -> Checking a
suppressGraph = wrapper2 (\case
  (AddNode _ _) -> Just ()
  (Wire _) -> Just ()
  _ -> Nothing)

inLvl :: String -> Checking a -> Checking a
inLvl prefix c = req (SplitNS prefix) >>= \prefixNamespace -> localNS prefixNamespace c

localNS :: Namespace -> Checking a -> Checking a
localNS _ (Ret v) = Ret v
localNS ns (Req (Fresh str) k) = let (name, root) = fresh str ns in
  localNS root (k name)
localNS ns (Req (SplitNS str) k) = let (subSpace, newRoot) = split str ns in
                                      localNS newRoot (k subSpace)
localNS ns (Req AskNS k) = localNS ns (k (fst ns))
localNS ns (Req c k) = Req c (localNS ns . k)
localNS ns (Define lbl e v k) = Define lbl e v (localNS ns . k)
localNS ns (Yield st k) = Yield st (localNS ns . k)
localNS ns (Fork desc par c) = let (subSpace, newRoot) = split desc ns in
                                 Fork desc (localNS subSpace par) (localNS newRoot c)

defineEnd :: String -> End -> Val Z -> Checking ()
defineEnd lbl e v = Define lbl e v (const (Ret ()))
