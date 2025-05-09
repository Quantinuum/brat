{-# LANGUAGE UndecidableInstances #-}

module Brat.Syntax.Raw where

import Control.Monad (unless, when)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor
import Data.Kind (Type)
import Data.List.NonEmpty (fromList, NonEmpty(..))
import Data.Map (disjoint, member, union)
import qualified Data.Map as M
import Data.Tuple.HT (thd3)

import Bwd
import Brat.Constructors
import Brat.Error
import Brat.FC hiding (end)
import Brat.Naming
import Brat.QualName
import Brat.Syntax.CircuitProperties
import Brat.Syntax.Common
import Brat.Syntax.Core
import Brat.Syntax.FuncDecl (FunBody(..), FuncDecl(..))
import Brat.Syntax.Simple
import Util (names, (**^))

type family TypeOf (k :: Kind) :: Type where
  TypeOf Noun = [InOut]
  TypeOf UVerb = CType

type RawVType = Raw Chk Noun

type RawIO = TypeRowElem (KindOr RawVType)

type RawCType = CType' RawIO
type RawKType = CType' (TypeRowElem RawVType)

data TypeAliasF tm = TypeAlias FC QualName [(PortName,TypeKind)] tm deriving Show
type RawAlias = TypeAliasF (Raw Chk Noun)
type TypeAlias = TypeAliasF (Term Chk Noun)

type TypeAliasTable = M.Map QualName TypeAlias

type RawEnv = ([RawFuncDecl], [RawAlias], TypeAliasTable)
type RawFuncDecl = FuncDecl [RawIO] (FunBody Raw Noun)

addNames :: TypeRow ty -> [(PortName, ty)]
addNames tms = aux (fromList names) tms
 where
  -- aux is passed the infinite list `names`, so we can use the partial function
  -- `fromList` to repeatedly convert it to NonEmpty so GHC doesn't complain
  -- about the missing case `aux [] _`
  aux (n :| ns) ((Anon tm):tms) = (n, tm) : aux (fromList ns) tms
  aux ns ((Named n tm):tms)  = (n, tm) : aux ns tms
  aux _ [] = []

data Raw :: Dir -> Kind -> Type where
  RSimple   :: SimpleTerm -> Raw Chk Noun
  RLet      :: WC Abstractor -> WC (Raw Syn Noun) -> WC (Raw d k) -> Raw d k
  RNHole    :: String -> Raw Chk Noun
  RVHole    :: String -> Raw Chk UVerb
  REmpty    :: Raw Chk Noun
  RPass     :: Raw Syn UVerb
  (::|::)   :: WC (Raw d k) -> WC (Raw d k) -> Raw d k
  RTh       :: WC (Raw Chk UVerb) -> Raw Chk Noun
  RTypedTh  :: WC (Raw Syn KVerb) -> Raw Syn Noun
  RForce    :: WC (Raw Syn Noun) -> Raw Syn KVerb
  REmb      :: WC (Raw Syn k) -> Raw Chk k
  RForget   :: WC (Raw d KVerb) -> Raw d UVerb
  RPull     :: [PortName] -> WC (Raw Chk k) -> Raw Chk k
  RVar      :: QualName -> Raw Syn Noun
  RIdentity :: Raw Syn UVerb
  RHope     :: Raw Chk Noun
  RArith    :: ArithOp -> WC (Raw Chk Noun) -> WC (Raw Chk Noun) -> Raw Chk Noun
  ROf       :: WC (Raw Chk Noun) -> WC (Raw d Noun) -> Raw d Noun
  (:::::)   :: WC (Raw Chk Noun) -> [RawIO] -> Raw Syn Noun
  (::-::)   :: WC (Raw Syn k) -> WC (Raw d UVerb) -> Raw d k -- vertical juxtaposition (diagrammatic composition)
  (::$::)   :: WC (Raw d KVerb) -> WC (Raw Chk k) -> Raw d k -- Eval with ChkRaw n argument
  RLambda   :: (WC Abstractor, WC (Raw d Noun)) -> [(WC Abstractor, WC (Raw Chk Noun))] -> Raw d UVerb
  RCon      :: QualName -> WC (Raw Chk Noun) -> Raw Chk Noun
  -- Function types
  RFn       :: RawCType -> Raw Chk Noun
  -- Kernel types
  RKernel   :: Properties Kernel -> RawKType -> Raw Chk Noun
  RFanOut   :: Raw Syn UVerb
  RFanIn    :: Raw Chk UVerb

class Dirable d where
  dir :: Raw d k -> Diry d

class Kindable k where
  kind :: Raw d k -> Kindy k

instance (Dirable Syn) where dir _ = Syny
instance (Dirable Chk) where dir _ = Chky
instance (Kindable Noun) where kind _ = Nouny
instance (Kindable UVerb) where kind _ = UVerby
instance (Kindable KVerb) where kind _ = KVerby

instance Show (Raw d k) where
  show (RLet abs xs body)
    = unwords ["let", show abs, "=", show xs, "in", show body]
  show (RNHole name) = '?':name
  show (RVHole name) = '?':name
  show RHope = "!"
  show (RSimple tm) = show tm
  show RPass = show "pass"
  show REmpty = "()"
  show (a ::|:: b) = show a ++ ", " ++ show b
  show (RTh comp) = '{' : show comp ++ "}"
  show (RTypedTh comp) = "{:" ++ show comp ++ ":}"
  show (RForce comp) = "Force " ++ show comp
  show (RForget kv) = "(Forget " ++ show kv ++ ")"
  show (REmb x) = '「' : show x ++ "」"
  show (RPull [] x) = "[]:" ++ show x
  show (RPull ps x) = concatMap (++":") ps ++ show x
  show (RVar x) = show x
  show RIdentity = "|"
  show (RArith op a b) = "(" ++ show op ++ " " ++ show a ++ " " ++ show b ++ ")"
  show (fun ::$:: arg) = show fun ++ ('(' : show arg ++ ")")
  show (tm ::::: ty) = show tm ++ " :: " ++ show ty
  show (a ::-:: b) = show a ++ "; " ++ show b
  show (RLambda c cs) = unlines (showClause c : (("| "++) . showClause <$> cs))
   where
    showClause :: forall d k. (WC Abstractor, WC (Raw d k)) -> String
    showClause (abs, bod) = show abs ++ " => " ++ show bod
  show (RCon c xs) = "Con(" ++ show c ++ "(" ++ show xs ++ "))"
  show (RFn cty) = show cty
  show (RKernel _ cty) = show cty
  show RFanOut = "[/\\]"
  show RFanIn = "[\\/]"
  show (ROf n e) = "(" ++ show n ++ " of " ++ show e ++ ")"

type Desugar = StateT Namespace (ReaderT (RawEnv, Bwd QualName) (Except Error))

-- instance {-# OVERLAPPING #-} MonadFail Desugar where
instance {-# OVERLAPPING #-} MonadFail Desugar where
  fail = throwError . desugarErr

freshM :: String -> Desugar Name
freshM str = do
  ns <- get
  let (name, ns') = fresh str ns
  put ns'
  pure name

splitM :: String -> Desugar Namespace
splitM s = do
  ns <- get
  let (ns', newRoot) = split s ns
  put newRoot
  pure ns'

isConstructor :: QualName -> Desugar Bool
isConstructor c = pure (c `member` defaultConstructors
                        || (Brat, c) `member` defaultTypeConstructors
                        || (Kernel, c) `member` defaultTypeConstructors
                        || c `member` natConstructors)

isAlias :: QualName -> Desugar Bool
isAlias name = do
  aliases <- asks (thd3 . fst)
  pure $ M.member name aliases


{-
findDuplicates :: Env -> Desugar ()
findDuplicates (ndecls, vdecls, aliases)
  = aux $ concat [(fst &&& show . fst . snd) <$> (unWC <$> ndecls)
                 ,(fst &&& show . fst . snd) <$> (unWC <$> vdecls)
                 ,(fst &&& show . snd) <$> aliases]
 where
  aux :: [(String, String)] -> Desugar ()
  aux xs = case filter ((1<).length) [ filter ((==x).fst) xs | (x,_) <- xs ] of
             []  -> pure () -- all good
             ([]:_) -> undefined -- this should be unreachable
             -- TODO: Include FC
             ((x:xs):_) -> desugarErr . unlines $ (("Multiple definitions of " ++ fst x)
                                                   :(snd <$> (x:xs))
                                                  )
-}

desugarErr :: String -> Error
desugarErr = dumbErr . DesugarErr

class Desugarable ty where
  type Desugared ty
  desugar :: WC ty -> Desugar (WC (Desugared ty))
  desugar (WC fc tm)
    = (WC fc <$> desugar' tm)
      `catchError`
      (\(Err _ msg) -> throwError (Err (Just fc) msg))

  desugar' :: ty -> Desugar (Desugared ty)

instance Desugarable ty => Desugarable (TypeRow ty) where
  type Desugared (TypeRow ty) = TypeRow (Desugared ty)
  desugar' = traverse (traverse desugar')

instance (Kindable k) => Desugarable (Raw d k) where
  type Desugared (Raw d k) = Term d k
  -- TODO: holes need to know their arity for type checking
  desugar' (RNHole strName) = NHole . (strName,) <$> freshM strName
  desugar' (RVHole strName) = VHole . (strName,) <$> freshM strName
  desugar' RHope = pure Hope
  desugar' RPass = pure Pass
  desugar' (RSimple simp) = pure $ Simple simp
  desugar' REmpty = pure Empty
  desugar' (a ::|:: b) = (:|:) <$> desugar a <*> desugar b
  desugar' (RTh v) = Th <$> desugar v
  desugar' (RTypedTh v) = TypedTh <$> desugar v
  {- As well as geniune embeddings of variables and applications, we have two
  other cases which will show up here:
   1. Constructors - either nullary or fully applied
   2. Type Aliases - either nullary or fully applied
  We check for both of these cases by looking up the variable in the relevant
  table of either known constructors or known type aliases. We must transform
  these into `Con c arg` when desugaring.
  -}
  desugar' (REmb syn) = case unWC syn of
    (WC _ (RForce (WC _ (RVar c)))) ::$:: a -> do
      isConOrAlias c >>= \case
        True -> case kind $ unWC a of
          Nouny -> Con c <$> desugar a
          _ -> throwError $ desugarErr "Constructor applied to something that isn't a noun"
        False -> Emb <$> desugar syn
    (RVar c) -> do
      isConOrAlias c >>= \case
        True -> pure $ Con c (WC (fcOf syn) Empty)
        False -> Emb <$> desugar syn
    _ -> Emb <$> desugar syn
  desugar' (RForce v) = Force <$> desugar v
  desugar' (RForget kv) = Forget <$> desugar kv
  desugar' (RPull ps raw) = Pull ps <$> desugar raw
  desugar' (RVar name) = pure $ Var name
  desugar' RIdentity = pure Identity
  desugar' (RArith op a b) = Arith op <$> desugar a <*> desugar b
  desugar' (fun ::$:: arg) = (:$:) <$> desugar fun <*> desugar arg
  desugar' (tm ::::: outputs) = do
    tm <- desugar tm
    (tys, ()) <- desugarBind outputs $ pure ()
    pure (tm ::: tys)
  desugar' (syn ::-:: verb) = (:-:) <$> desugar syn <*> desugar verb
  desugar' (RLambda c cs) = Lambda <$> (id **^ desugar) c <*> traverse (id **^ desugar) cs
  desugar' (RLet abs thing body) = Let abs <$> desugar thing <*> desugar body
  desugar' (RCon c arg) = Con c <$> desugar arg
  desugar' (RFn cty) = C <$> desugar' cty
  desugar' (RKernel props cty) = K props <$> desugar' cty
  desugar' RFanOut = pure FanOut
  desugar' RFanIn = pure FanIn
  desugar' (ROf n e) = Of <$> desugar n <*> desugar e

instance Desugarable ty => Desugarable (PortName, ty) where
  type Desugared (PortName, ty) = (PortName, Desugared ty)
  desugar' (p, ty) = (p,) <$> desugar' ty

instance Desugarable (CType' (TypeRowElem RawVType)) where
  type Desugared (CType' (TypeRowElem RawVType)) = CType' (PortName, Term Chk Noun)
  desugar' (ss :-> ts) = do
    ss <- traverse desugar' (addNames ss)
    ts <- traverse desugar' (addNames ts)
    pure (ss :-> ts)

isConOrAlias :: QualName -> Desugar Bool
isConOrAlias c = do
  con <- isConstructor c
  ali <- isAlias c
  xor con ali
 where
  -- Double check that we don't have name clashes. This should never
  -- happen since we already detect them in `desugarAliases` before
  -- this function is called.
  xor :: Bool -> Bool -> Desugar Bool
  xor True True = throwError $
                  dumbErr $
                  InternalError "Name clash between type constructor and type alias"
  xor a b = pure (a || b)


instance Desugarable ty => Desugarable (KindOr ty) where
  type Desugared (Either TypeKind ty) = Either TypeKind (Desugared ty)
  desugar' (Left k) = pure (Left k)
  desugar' (Right ty) = Right <$> desugar' ty

desugarBind :: forall t. [RawIO]
            -> Desugar t
            -> Desugar ([(PortName, KindOr (Term Chk Noun))], t)
desugarBind tys m = worker (addNames tys)
 where
  worker :: [(PortName, KindOr (Raw Chk Noun))]
         -> Desugar ([(PortName, KindOr (Term Chk Noun))], t)
  worker ((p, Left k):ns) = do
    (ns, t) <- local (second (:< PrefixName [] p)) $ worker ns
    pure ((p, Left k):ns, t)
  worker ((p, Right ty):ns) = do
    ty <- desugar' ty
    (ns, t) <- worker ns
    pure ((p, Right ty):ns, t)
  worker [] = ([],) <$> m

instance Desugarable (CType'  RawIO) where
  type Desugared (CType' RawIO) = CType' (PortName, KindOr (Term Chk Noun))
  desugar' (ss :-> ts) = do
    (ss, (ts, ())) <- desugarBind ss $ desugarBind ts $ pure ()
    pure $ ss :-> ts

instance Desugarable RawAlias where
  type Desugared RawAlias = TypeAlias
  desugar' (TypeAlias fc name args def) = TypeAlias fc name args <$> desugar' def

desugarNBody :: FunBody Raw Noun -> Desugar (FunBody Term Noun)
desugarNBody (ThunkOf clause)
  = ThunkOf <$> traverse desugarVBody clause
desugarNBody (NoLhs body) = NoLhs <$> desugar body
desugarNBody Undefined = pure Undefined

desugarVBody :: FunBody Raw UVerb -> Desugar (FunBody Term UVerb)
desugarVBody (Clauses cs) = Clauses <$> mapM branch cs
 where
  branch :: (WC Abstractor, WC (Raw Chk Noun)) -> Desugar (WC Abstractor, WC (Term Chk Noun))
  branch (lhs, rhs) = (lhs,) <$> desugar rhs
desugarVBody (NoLhs rhs) = NoLhs <$> desugar rhs
desugarVBody Undefined = pure Undefined

instance Desugarable RawFuncDecl where
  type Desugared RawFuncDecl = CoreFuncDecl
  desugar' d@FuncDecl{..} = do
    tys  <- addNames <$> desugar' fnSig
    noun <- desugarNBody fnBody
    pure $ d { fnBody = noun
             , fnSig  = tys
             }

mkAliasTbl :: [TypeAlias] -> TypeAliasTable
mkAliasTbl [] = M.empty
mkAliasTbl (a@(TypeAlias _ name _ _):as) = M.insert name a (mkAliasTbl as)

desugarAliases :: [RawAlias] -> Desugar [TypeAlias]
desugarAliases [] = pure []
desugarAliases (a@(TypeAlias fc name _ _):as) = do
  nameExists <- liftA2 (||) (isConstructor name) (isAlias name)
  when nameExists (throwError (Err (Just fc) (NameClash $ "Identifier `" ++ show name ++ "` is already used")))
  a@(TypeAlias _ name _ _) <- desugar' a
  local (\((decls, aliases, aliasTbl), uz) -> ((decls, aliases, M.insert name a aliasTbl), uz)) $
    (a :) <$> desugarAliases as

desugarEnv :: RawEnv -> Either Error ([CoreFuncDecl], [TypeAlias])
desugarEnv env@(decls, aliases, aliasTbl)
  = fmap fst
    . runExcept
    . flip runReaderT (env, B0)
    . flip runStateT root
    $ do
  -- Desugar aliases
  aliases <- desugarAliases aliases
  let newAliasTbl = mkAliasTbl aliases
  unless (disjoint aliasTbl newAliasTbl) $ fail "illegally named alias"
  decls <- local (\((decls, aliases, aliasTbl), uz) -> ((decls, aliases, newAliasTbl `union` aliasTbl),uz)) $
              traverse desugar' decls
  pure (decls, aliases)
