module Brat.Elaborator (dir, elabEnv, elaborate, kind, runElab, SomeTerm(..)) where

import Control.Monad ((>=>))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Functor ((<&>))
import Data.Maybe (fromMaybe)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Tuple.HT (thd3)
import qualified Data.Map as M

import Bwd
import Brat.Constructors
import Brat.Error
import Brat.FC
import Brat.Naming (fresh, Name, Namespace)
import Brat.QualName (QualName)
import Brat.Syntax.Common
import Brat.Syntax.Concrete
import Brat.Syntax.Core (Term(..), TypeAlias)
import Brat.Syntax.FuncDecl (FunBody(..), FuncDecl(..))

class Dirable d where
  dir :: Term d k -> Diry d

class Kindable k where
  kind :: Term d k -> Kindy k

instance (Dirable Syn) where dir _ = Syny
instance (Dirable Chk) where dir _ = Chky
instance (Kindable Noun) where kind _ = Nouny
instance (Kindable UVerb) where kind _ = UVerby
instance (Kindable KVerb) where kind _ = KVerby

type Env = ([TermFuncDecl], [TypeAlias], TypeAliasTable)

type Elab = StateT Namespace (ReaderT (Env, Bwd QualName) (Except Error))

type TermFuncDecl = FuncDecl (TypeRow (KindOr (Term Chk Noun))) (FunBody Term Noun)

type TypeAliasTable = M.Map QualName TypeAlias

freshM :: String -> Elab Name
freshM str = do
  ns <- get
  let (name, ns') = fresh str ns
  put ns'
  pure name

isConstructor :: QualName -> Elab Bool
isConstructor c = pure (c `M.member` defaultConstructors
                        || (Brat, c) `M.member` defaultTypeConstructors
                        || (Kernel, c) `M.member` defaultTypeConstructors
                        || c `M.member` natConstructors)

isAlias :: QualName -> Elab Bool
isAlias name = do
  aliases <- asks (thd3 . fst)
  pure $ M.member name aliases

isConOrAlias :: QualName -> Elab Bool
isConOrAlias c = do
  con <- isConstructor c
  ali <- isAlias c
  xor con ali
 where
  -- Double check that we don't have name clashes. This should never
  -- happen since we already detect them in `desugarAliases` before
  -- this function is called.
  xor :: Bool -> Bool -> Elab Bool
  xor True True = throwError $
                  dumbErr $
                  InternalError "Name clash between type constructor and type alias"
  xor a b = pure (a || b)

assertSyn :: Dirable d => WC (Term d k) -> Elab (WC (Term Syn k))
assertSyn s@(WC fc r) = case dir r of
  Syny -> pure s
  Chky -> throwError $ Err (Just fc) (ElabErr "Cannot synthesise a type for this expression")

assertChk :: Dirable d => WC (Term d k) -> Elab (WC (Term Chk k))
assertChk s@(WC _ r) = case dir r of
  Syny -> deepEmb s
  Chky -> pure s
 where
  -- Add embedding as deep as possible
  {- As well as geniune embeddings of variables and applications, we have two
  other cases which will show up here:
   1. Constructors - either nullary or fully applied
   2. Type Aliases - either nullary or fully applied
  We check for both of these cases by looking up the variable in the relevant
  table of either known constructors or known type aliases. We must transform
  these into `Con c arg` when desugaring.
  -}
  deepEmb :: WC (Term Syn k) -> Elab (WC (Term Chk k))
  deepEmb (WC fc tm) = WC fc <$> case tm of
    a :|: b -> (:|:) <$> deepEmb a <*> deepEmb b
    a :-: b -> (a :-:) <$> deepEmb b
{-
    (Force (WC _ (Var c))) :$: a -> isConOrAlias c >>= \case
      True -> case kind $ unWC a of
        Nouny -> pure $ Con c a
        _ -> throwError $ desugarErr "Constructor applied to something that isn't a noun"
      False -> pure $ Emb (WC fc tm)
-}
    Lambda (a,c) cs -> (\c -> Lambda (a,c) cs) <$> deepEmb c
    Let abs a b -> Let abs a <$> deepEmb b
    Of num exp -> Of num <$> deepEmb exp
  -- We like to avoid RTypedTh because the body doesn't know whether it's Brat or Kernel
    TypedTh bdy -> Th . WC fc . Forget <$> deepEmb bdy
    Var c -> isConOrAlias c <&> \case
      True  -> Con c (WC fc Empty)
      False -> Emb (WC fc (Var c))
    a -> pure $ (Emb (WC fc a))

assertNoun :: Kindable k => WC (Term d k) -> Either Error (WC (Term d Noun))
assertNoun s@(WC fc r) = case kind r of
  Nouny -> pure s
  _ -> Left $ Err (Just fc) (ElabErr "Noun required at this position")

-- Note that we don't force holes, instead we directly turn them into verbs
assertUVerb :: (Dirable d, Kindable k) => WC (Term d k) -> Either Error (WC (Term d UVerb))
assertUVerb (WC fc (NHole x)) = pure $ WC fc (VHole x)
assertUVerb s@(WC fc r) = case kind r of
  UVerby -> pure s
  _ -> WC fc . Forget <$> assertKVerb s

assertKVerb :: (Dirable d, Kindable k) => WC (Term d k) -> Either Error (WC (Term d KVerb))
assertKVerb s@(WC fc r) = case kind r of
  UVerby -> Left $ Err (Just fc) (ElabErr "Verb cannot synthesize its argument types")
  KVerby -> pure s
  Nouny -> case dir r of
    Syny -> pure $ WC fc (Force s)
    Chky -> Left $ Err (Just fc) (ElabErr "Verb required at this position (cannot force since the type cannot be synthesised)")

mkCompose :: (Dirable d1, Kindable k1, Dirable d2, Kindable k2)
          => WC (Term d1 k1) -> WC (Term d2 k2)
          -> Elab SomeTerm'
mkCompose a f = do
  -- There are two ways we could elaborate (f: KVerb) applied to (a: Syn).
  -- Either (Emb a) or (Forget f) is possible, but we prefer (Emb a),
  -- as this makes it easier to spot applications of constructors in desugaring.
  case assertKVerb f of
    Right f -> do  -- traditionally `f(a)`: intermediate type from f
      a <- assertChk a
      pure $ SomeTerm' (f :$: a)
    Left _ -> do -- traditionally 'a |> f' or 'a;f': intermediate type from a
      a <- assertSyn a
      f <- liftEither (assertUVerb f)
      pure $ SomeTerm' (a :-: f)

elaborateChkNoun :: WC Flat -> Elab (WC (Term Chk Noun))
elaborateChkNoun = elaborate >=> (\(SomeTerm raw) -> liftEither (assertNoun raw) >>= assertChk)

data SomeTerm where
  SomeTerm :: (Dirable d, Kindable k) => WC (Term d k) -> SomeTerm

data SomeTerm' where
  SomeTerm' :: (Dirable d, Kindable k) => Term d k -> SomeTerm'

elaborate :: WC Flat -> Elab SomeTerm
-- All legal underscores should have been replaced with
-- dummy variables '0, '1, '2 .... by now
elaborate (WC fc FUnderscore) = throwError (Err (Just fc) (ParseErr (PE "unexpected _")))
elaborate (WC fc x) = do
  SomeTerm' x <- elaborate' x
  pure $ SomeTerm (WC fc x)

elaborate' :: Flat -> Elab SomeTerm'
elaborate' (FVar x) = pure $ SomeTerm' (Var x)
elaborate' (FHope ident) = pure $ SomeTerm' (Hope ident)
elaborate' (FArith op a b) = do
  (SomeTerm a) <- elaborate a
  (SomeTerm b) <- elaborate b
  a <- assertChk a
  b <- assertChk b
  a <- liftEither $ assertNoun a
  b <- liftEither $ assertNoun b
  pure $ SomeTerm' (Arith op a b)
elaborate' (FApp f a) = do
  (SomeTerm f) <- elaborate f
  (SomeTerm a) <- elaborate a
  a <- liftEither $ assertNoun a
  mkCompose a f
elaborate' (FJuxt a b) = do
  (SomeTerm a) <- elaborate a
  (SomeTerm b) <- elaborate b
  case (kind (unWC a), kind (unWC b)) of
    (Nouny, Nouny) -> unifyDir a b
    _ -> case (assertKVerb a, assertKVerb b) of
         -- nothing can be coerced to a noun, so try coercing both to the next best thing
      (Right a, Right b) -> unifyDir a b
      _ -> do -- at least one cannot be coerced to KVerb
        a <- liftEither $ assertUVerb a
        b <- liftEither $ assertUVerb b
        unifyDir a b
 where
  unifyDir :: (Dirable d1, Dirable d2, Kindable k)
            => WC (Term d1 k) -> WC (Term d2 k)
            -> Elab SomeTerm'
  unifyDir r1 r2 = case (dir (unWC r1), dir (unWC r2)) of
    (Syny, Syny) -> pure $ SomeTerm' (r1 :|: r2)
    _ -> do
      r1 <- assertChk r1
      r2 <- assertChk r2
      pure $ SomeTerm' (r1 :|: r2)
elaborate' FPass = pure $ SomeTerm' Pass
elaborate' (FThunk a) = do
  (SomeTerm a) <- elaborate a
  let alt = do
        a <- liftEither $ assertUVerb a
        a <- assertChk a
        pure $ SomeTerm' (Th a)
  -- Assert verb before chk since force needs to come before emb
  flip catchError (const alt) $ do
    a <- assertSyn =<< liftEither (assertKVerb a)
    pure (SomeTerm' (TypedTh a))
elaborate' (FCompose a b) = do
  (SomeTerm a) <- elaborate a
  (SomeTerm b) <- elaborate b
  -- The LHS must be a UVerb *or* KVerb, perhaps by implicit forcing
  (SomeTerm a) <- case assertKVerb a of
    Right a -> pure $ SomeTerm a
    Left _ -> liftEither $ SomeTerm <$> assertUVerb a
  mkCompose a b
elaborate' (FLambda ((abs,rhs) :| cs)) = do
  SomeTerm rhs <- elaborate rhs
  rhs <- liftEither $ assertNoun rhs
  cs <- traverse elaborateClause cs
  pure $ SomeTerm' (Lambda (abs,rhs) cs)
 where
  elaborateClause :: (WC Abstractor, WC Flat) -> Elab (WC Abstractor, WC (Term Chk Noun))
  elaborateClause (abs, e) = do
    SomeTerm a <- elaborate e
    a <- assertChk =<< liftEither (assertNoun a)
    pure (abs, a)

elaborate' (FLetIn abs a b) = do
  (SomeTerm a) <- elaborate a
  (SomeTerm b) <- elaborate b
  a <- assertSyn a
  a <- liftEither $ assertNoun a
  pure $ SomeTerm' (Let abs a b)
elaborate' (FSimple t) = pure $ SomeTerm' (Simple t)
-- Holes are elaborated as nouns and can be turned into verbs by assertVerb
elaborate' (FHole x) = SomeTerm' . NHole . (x,) <$> freshM x
elaborate' (FCon n a) = do
  (SomeTerm a) <- elaborate a
  a <- assertChk a
  a <- liftEither $ assertNoun a
  pure $ SomeTerm' (Con n a)
elaborate' FEmpty = pure $ SomeTerm' Empty
elaborate' (FPull ps a) = do
  (SomeTerm a) <- elaborate a
  a <- assertChk a
  pure $ SomeTerm' (Pull ps a)
elaborate' (FAnnotation a ts) = do
  (SomeTerm a) <- elaborate a
  a <- assertChk a
  a <- liftEither $ assertNoun a
  ts <- fmap (fmap unWC) <$> traverse elabSigElem ts
  pure $ SomeTerm' (a ::: ts)
elaborate' (FInto a b) = elaborate' (FApp b a)
elaborate' (FOf n e) = do
  SomeTerm n <- elaborate n
  n <- assertChk n
  n <- liftEither $ assertNoun n
  SomeTerm e <- elaborate e
  e <- liftEither $ assertNoun e
  pure $ SomeTerm' (Of n e)
elaborate' (FFn cty) = SomeTerm' . C . fmap (fmap unWC) <$> traverse elabSigElem cty
elaborate' (FKernel cty) = SomeTerm' . K . fmap (fmap unWC) <$> traverse elabSigElem cty
elaborate' FIdentity = pure $ SomeTerm' Identity
-- We catch underscores in the top-level elaborate so this case
-- should never be triggered
elaborate' FUnderscore = throwError (dumbErr (InternalError "Unexpected '_'"))
elaborate' FFanOut = pure $ SomeTerm' FanOut
elaborate' FFanIn = pure $ SomeTerm' FanIn
class Elaborable t where
  type Elaborated t
  elab :: WC t -> Elab (WC (Elaborated t))

-- This is a hack to make elabSigElem nice
instance Elaborable Flat where
  type Elaborated Flat = Term Chk Noun
  elab = elaborateChkNoun

instance Elaborable t => Elaborable (KindOr t) where
  type Elaborated (KindOr t) = KindOr (Elaborated t)
  elab (WC fc (Left k)) = pure (WC fc (Left k))
  elab (WC fc (Right ty)) = fmap Right <$> elab (WC fc ty)

elabSigElem :: Elaborable t
            => TypeRowElem (WC t)
            -> Elab (TypeRowElem (WC (Elaborated t)))
elabSigElem (Anon ty) = Anon <$> elab ty
elabSigElem (Named p ty) = Named p <$> elab ty

elabBody :: FBody -> FC -> Elab (FunBody Term Noun)
elabBody (FClauses cs) fc = ThunkOf . WC fc . Clauses <$> traverse elab1Clause cs
 where
  elab1Clause :: (WC Abstractor, WC Flat)
              -> Elab (WC Abstractor, WC (Term Chk Noun))
  elab1Clause (abs, tm) = do
    SomeTerm tm <- elaborate tm
    tm <- liftEither $ assertNoun tm
    tm <- assertChk tm
    pure (abs, tm)
elabBody (FNoLhs e) _ = do
    SomeTerm e <- elaborate e
    e <- assertChk e
    case kind (unWC e) of
      Nouny -> pure $ NoLhs e
      _ -> case assertUVerb e of
        Right e -> pure $ ThunkOf (WC (fcOf e) (NoLhs e))
        Left err -> throwError err
elabBody FUndefined _ = pure Undefined

elabFunDecl :: FDecl -> Elab TermFuncDecl
elabFunDecl d = do
  rc <- elabBody (fnBody d) (fnLoc d)
  sig <- traverse elabSigElem (fnSig d)
  pure $ FuncDecl
    { fnName = fnName d
    , fnLoc = fnLoc d
    , fnSig = fmap unWC <$> sig -- sus
    , fnBody = rc
    , fnLocality = fnLocality d
    }

elabAlias :: FAlias -> Elab TypeAlias
elabAlias (TypeAlias fc name tys tm) = TypeAlias fc name tys . unWC <$> elaborateChkNoun (WC fc tm)

{-
mkAliasTbl :: [TypeAlias] -> TypeAliasTable
mkAliasTbl [] = M.empty
mkAliasTbl (a@(TypeAlias _ name _ _):as) = M.insert name a (mkAliasTbl as)
-}

runElab :: Maybe (Env, Bwd QualName) -> Namespace -> Elab a -> Either Error a
runElab env ns e =
  runExcept $
  flip runReaderT (fromMaybe (emptyEnv, B0) env) $
  evalStateT e ns
 where
  emptyEnv :: Env
  emptyEnv = ([], [], M.empty)

elabEnv :: Namespace -> FEnv -> Either Error ([TermFuncDecl], [TypeAlias])
elabEnv ns (ds, as) = runElab Nothing ns $ do
  ds <- traverse elabFunDecl ds
  as <- traverse elabAlias as
  pure (ds,as)
