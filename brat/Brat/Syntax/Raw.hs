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
import Brat.Checker.Arithmetic
import Brat.Constructors
import Brat.Error
import Brat.FC hiding (end)
import Brat.Naming
import Brat.QualName
import Brat.Syntax.Common
import Brat.Syntax.Core
import Brat.Syntax.FuncDecl (FunBody(..), FuncDecl(..))
import Brat.Syntax.Simple
import Brat.Syntax.Value (NumFun(numValue), NumSum(..), NumVal, nFull, nPlus, n2PowTimes, nVar, nv_to_sum)
import Util (log2, names, (**^))

type family TypeOf (k :: Kind) :: Type where
  TypeOf Noun = [InOut]
  TypeOf UVerb = CType

type RawVType = Raw Chk Noun

-- Raw stuff that's also used in Brat.Syntax.Concrete
type RawIO = TypeRowElem (WC RawVType) (KindOr RawVType)

type RawCType = CType' RawIO
type RawKType = CType' (TypeRowElem (WC RawVType) RawVType)

type TypeAlias = TypeAliasF (Term Chk Noun)

type TypeAliasTable = M.Map QualName TypeAlias

type RawAlias = TypeAliasF (Raw Chk Noun)


type RawEnv = ([RawFuncDecl], [RawAlias], TypeAliasTable)
type RawFuncDecl = FuncDecl [RawIO] (FunBody Raw Noun)
type CoreFuncDecl = FuncDecl (TypeRow TermConstraint (KindOr (Term Chk Noun))) (FunBody Term Noun)

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
  RKernel   :: RawKType -> Raw Chk Noun
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
  show (RKernel cty) = show cty
  show RFanOut = "[/\\]"
  show RFanIn = "[\\/]"
  show (ROf n e) = "(" ++ show n ++ " of " ++ show e ++ ")"

type Desugar = StateT Namespace (ReaderT (RawEnv, Bwd QualName) (Except Error))

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

instance Desugarable ty => Desugarable (TypeRowElem (WC RawVType) ty) where
    type Desugared (TypeRowElem (WC RawVType) ty) = TypeRowElem TermConstraint (Desugared ty)
    desugar' (Anon ty) = Anon <$> desugar' ty
    desugar' (Named x ty) = Named x <$> desugar' ty
    desugar' (Constraint a b) = case (,) <$> elabArith a <*> elabArith b of
      Left e -> throwError e
      Right (a,b) -> pure (Constraint a b)
     where
      elabArith :: WC RawVType -> Either Error (NumSum QualName)
      elabArith (WC _ (REmb (WC _ (RVar x)))) = pure (nsVar x)
      elabArith (WC fc (RArith Add a b)) = do
        nsa <- elabArith a
        nsb <- elabArith b
        pure (nsa <> nsb)
      elabArith (WC fc (RArith Mul a b)) = do
        nsa <- elabArith a
        nsb <- elabArith b
        case (isScalar nsa, isScalar nsb) of
          (Just n, _) -> pure $ nsb `nsMul` n
          (_, Just n) -> pure $ nsa `nsMul` n
          _ -> Left $ Err (Just fc) (DesugarErr "Arithmetic too confusing")
      elabArith (WC fc (RArith Pow a b)) = do
        nsa <- elabArith a
        nsb <- elabArith b
        case (isScalar nsa, sumToVal nsb) of
          (Just 2, Just nv) -> pure $ nsConst 1 <> nv_to_sum (nFull nv)
          _ -> Left $ Err (Just fc) (DesugarErr "Arithmetic too confusing")
      elabArith (WC fc (RArith op _ _)) = Left $ Err (Just fc) (DesugarErr ("Operation " ++ show op ++ " not allowed in constraints"))
      elabArith (WC fc _) = Left $ Err (Just fc) (DesugarErr "Malformed arithmetic in constraint")

      isScalar :: NumSum QualName -> Maybe Integer
      isScalar (NumSum n []) = Just n
      isScalar _ = Nothing

      sumToVal :: NumSum QualName -> Maybe (NumVal QualName)
      sumToVal (NumSum up [(n, k)]) | Just l <- log2 k = Just $ nPlus up (n2PowTimes l (numValue n))
      sumToVal _ = Nothing

instance Desugarable (TypeRowElem con ty) => Desugarable [TypeRowElem con ty] where
  type Desugared [TypeRowElem con ty] = [Desugared (TypeRowElem con ty)]
  desugar' = traverse desugar'

-- Desugaring terms
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
    tys <- traverse desugar' outputs
    pure (tm ::: tys)
  desugar' (syn ::-:: verb) = (:-:) <$> desugar syn <*> desugar verb
  desugar' (RLambda c cs) = Lambda <$> (id **^ desugar) c <*> traverse (id **^ desugar) cs
  desugar' (RLet abs thing body) = Let abs <$> desugar thing <*> desugar body
  desugar' (RCon c arg) = Con c <$> desugar arg
  desugar' (RFn cty) = C <$> desugar' cty
  desugar' (RKernel cty) = K <$> desugar' cty
  desugar' RFanOut = pure FanOut
  desugar' RFanIn = pure FanIn
  desugar' (ROf n e) = Of <$> desugar n <*> desugar e

instance Desugarable (CType' (TypeRowElem (WC RawVType) RawVType)) where
  type Desugared (CType' (TypeRowElem (WC RawVType) RawVType)) = CType' (TypeRowElem TermConstraint (Term Chk Noun))
  desugar' :: CType' (TypeRowElem (WC RawVType) RawVType) -> Desugar (CType' (TypeRowElem TermConstraint (Term Chk Noun)))
  desugar' (ss :-> ts) = do
    ss <- traverse desugar' ss -- (addNames ss)
    ts <- traverse desugar' ts -- (addNames ts)
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

instance Desugarable (CType' RawIO) where
  type Desugared (CType' RawIO) = CType' (TypeRowElem TermConstraint (KindOr (Term Chk Noun)))
  desugar' (ss :-> ts) = (:->) <$> desugar' ss <*> desugar' ts

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
    tys  <- desugar' fnSig
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
