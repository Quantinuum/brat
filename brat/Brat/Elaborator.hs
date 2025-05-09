module Brat.Elaborator where

import Control.Monad (forM, (>=>))
import Data.Bifunctor (second)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (empty)

import Brat.FC
import Brat.Syntax.Common
import Brat.Syntax.Concrete
import Brat.Syntax.FuncDecl (FunBody(..), FuncDecl(..))
import Brat.Syntax.Raw
import Brat.Error

assertSyn :: Dirable d => WC (Raw d k) -> Either Error (WC (Raw Syn k))
assertSyn s@(WC fc r) = case dir r of
  Syny -> pure s
  Chky -> Left $ Err (Just fc) (ElabErr "Cannot synthesise a type for this expression")

assertChk :: Dirable d => WC (Raw d k) -> Either Error (WC (Raw Chk k))
assertChk s@(WC _ r) = case dir r of
  Syny -> pure $ deepEmb s
  Chky -> pure s
 where
  -- Add embedding as deep as possible
  deepEmb :: WC (Raw Syn k) -> WC (Raw Chk k)
  deepEmb (WC fc (a ::|:: b)) = WC fc (deepEmb a ::|:: deepEmb b)
  deepEmb (WC fc (a ::-:: b)) = WC fc (a ::-:: deepEmb b)
  deepEmb (WC fc (RLambda c cs)) = WC fc (RLambda (second deepEmb c) cs)
  deepEmb (WC fc (RLet abs a b)) = WC fc (RLet abs a (deepEmb b))
  deepEmb (WC fc (ROf num exp)) = WC fc (ROf num (deepEmb exp))
  -- We like to avoid RTypedTh because the body doesn't know whether it's Brat or Kernel
  deepEmb (WC fc (RTypedTh bdy)) = WC fc (RTh (WC fc $ RForget $ deepEmb bdy))
  deepEmb (WC fc a) = WC fc (REmb (WC fc a))

assertNoun :: Kindable k => WC (Raw d k) -> Either Error (WC (Raw d Noun))
assertNoun s@(WC fc r) = case kind r of
  Nouny -> pure s
  _ -> Left $ Err (Just fc) (ElabErr "Noun required at this position")

-- Note that we don't force holes, instead we directly turn them into verbs
assertUVerb :: (Dirable d, Kindable k) => WC (Raw d k) -> Either Error (WC (Raw d UVerb))
assertUVerb (WC fc (RNHole x)) = pure $ WC fc (RVHole x)
assertUVerb s@(WC fc r) = case kind r of
  UVerby -> pure s
  _ -> WC fc . RForget <$> assertKVerb s

assertKVerb :: (Dirable d, Kindable k) => WC (Raw d k) -> Either Error (WC (Raw d KVerb))
assertKVerb s@(WC fc r) = case kind r of
  UVerby -> Left $ Err (Just fc) (ElabErr "Verb cannot synthesize its argument types")
  KVerby -> pure s
  Nouny -> case dir r of
    Syny -> pure $ WC fc (RForce s)
    Chky -> Left $ Err (Just fc) (ElabErr "Verb required at this position (cannot force since the type cannot be synthesised)")

mkCompose :: (Dirable d1, Kindable k1, Dirable d2, Kindable k2)
          => WC (Raw d1 k1) -> WC (Raw d2 k2)
          -> Either Error SomeRaw'
mkCompose a f = do
  -- There are two ways we could elaborate (f: KVerb) applied to (a: Syn).
  -- Either (Emb a) or (Forget f) is possible, but we prefer (Emb a),
  -- as this makes it easier to spot applications of constructors in desugaring.
  case assertKVerb f of
    Right f -> do  -- traditionally `f(a)`: intermediate type from f
      a <- assertChk a
      pure $ SomeRaw' (f ::$:: a)
    Left _ -> do -- traditionally 'a |> f' or 'a;f': intermediate type from a
      a <- assertSyn a
      f <- assertUVerb f
      pure $ SomeRaw' (a ::-:: f)

elaborateType :: WC Flat -> Either Error (WC (Raw Chk Noun))
elaborateType = elaborateChkNoun

elaborateChkNoun :: WC Flat -> Either Error (WC (Raw Chk Noun))
elaborateChkNoun = elaborate >=> (\(SomeRaw raw) -> assertNoun raw >>= assertChk)

data SomeRaw where
  SomeRaw :: (Dirable d, Kindable k) => WC (Raw d k) -> SomeRaw

data SomeRaw' where
  SomeRaw' :: (Dirable d, Kindable k) => Raw d k -> SomeRaw'

elaborate :: WC Flat -> Either Error SomeRaw
-- All legal underscores should have been replaced with
-- dummy variables '0, '1, '2 .... by now
elaborate (WC fc FUnderscore) = Left (Err (Just fc) (ParseErr (PE "unexpected _")))
elaborate (WC fc x) = do
  SomeRaw' x <- elaborate' x
  pure $ SomeRaw (WC fc x)

elaborate' :: Flat -> Either Error SomeRaw'
elaborate' (FVar x) = pure $ SomeRaw' (RVar x)
elaborate' FHope = pure $ SomeRaw' RHope
elaborate' (FArith op a b) = do
  (SomeRaw a) <- elaborate a
  (SomeRaw b) <- elaborate b
  a <- assertChk a
  b <- assertChk b
  a <- assertNoun a
  b <- assertNoun b
  pure $ SomeRaw' (RArith op a b)
elaborate' (FApp f a) = do
  (SomeRaw f) <- elaborate f
  (SomeRaw a) <- elaborate a
  a <- assertNoun a
  mkCompose a f
elaborate' (FJuxt a b) = do
  (SomeRaw a) <- elaborate a
  (SomeRaw b) <- elaborate b
  case (kind (unWC a), kind (unWC b)) of
    (Nouny, Nouny) -> unifyDir a b
    _ -> case (assertKVerb a, assertKVerb b) of
         -- nothing can be coerced to a noun, so try coercing both to the next best thing
      (Right a, Right b) -> unifyDir a b
      _ -> do -- at least one cannot be coerced to KVerb
        a <- assertUVerb a
        b <- assertUVerb b
        unifyDir a b
 where
  unifyDir :: (Dirable d1, Dirable d2, Kindable k)
            => WC (Raw d1 k) -> WC (Raw d2 k)
            -> Either Error SomeRaw'
  unifyDir r1 r2 = case (dir (unWC r1), dir (unWC r2)) of
    (Syny, Syny) -> pure $ SomeRaw' (r1 ::|:: r2)
    _ -> do
      r1 <- assertChk r1
      r2 <- assertChk r2
      pure $ SomeRaw' (r1 ::|:: r2)
elaborate' FPass = pure $ SomeRaw' RPass
elaborate' (FThunk a) = do
  (SomeRaw a) <- elaborate a
  case (assertKVerb >=> assertSyn) a of
    Right a -> pure $ SomeRaw' (RTypedTh a)
    Left _ -> do -- Assert verb before chk since force needs to come before emb
      a <- assertUVerb a
      a <- assertChk a
      pure $ SomeRaw' (RTh a)
elaborate' (FCompose a b) = do
  (SomeRaw a) <- elaborate a
  (SomeRaw b) <- elaborate b
  -- The LHS must be a UVerb *or* KVerb, perhaps by implicit forcing
  (SomeRaw a) <- case assertKVerb a of
    Right a -> pure $ SomeRaw a
    Left _ -> SomeRaw <$> assertUVerb a
  mkCompose a b
elaborate' (FLambda ((abs,rhs) :| cs)) = do
  SomeRaw rhs <- elaborate rhs
  rhs <- assertNoun rhs
  cs <- traverse elaborateClause cs
  pure $ SomeRaw' (RLambda (abs,rhs) cs)
 where
  elaborateClause :: (WC Abstractor, WC Flat) -> Either Error (WC Abstractor, WC (Raw Chk Noun))
  elaborateClause (abs, e) = do
    SomeRaw a <- elaborate e
    a <- assertChk =<< assertNoun a
    pure (abs, a)

elaborate' (FLetIn abs a b) = do
  (SomeRaw a) <- elaborate a
  (SomeRaw b) <- elaborate b
  a <- assertSyn a
  a <- assertNoun a
  pure $ SomeRaw' (RLet abs a b)
elaborate' (FSimple t) = pure $ SomeRaw' (RSimple t)
-- Holes are elaborated as nouns and can be turned into verbs by assertVerb
elaborate' (FHole x) = pure $ SomeRaw' (RNHole x)
elaborate' (FCon n a) = do
  (SomeRaw a) <- elaborate a
  a <- assertChk a
  a <- assertNoun a
  pure $ SomeRaw' (RCon n a)
elaborate' FEmpty = pure $ SomeRaw' REmpty
elaborate' (FPull ps a) = do
  (SomeRaw a) <- elaborate a
  a <- assertChk a
  pure $ SomeRaw' (RPull ps a)
elaborate' (FAnnotation a ts) = do
  (SomeRaw a) <- elaborate a
  a <- assertChk a
  a <- assertNoun a
  pure $ SomeRaw' (a ::::: ts)
elaborate' (FInto a b) = elaborate' (FApp b a)
elaborate' (FOf n e) = do
  SomeRaw n <- elaborate n
  n <- assertNoun =<< assertChk n
  SomeRaw e <- elaborate e
  e <- assertNoun e
  pure $ SomeRaw' (ROf n e)
elaborate' (FFn cty) = pure $ SomeRaw' (RFn cty)
elaborate' (FKernel ps sty) = pure $ SomeRaw' (RKernel ps sty)
elaborate' FIdentity = pure $ SomeRaw' RIdentity
-- We catch underscores in the top-level elaborate so this case
-- should never be triggered
elaborate' FUnderscore = Left (dumbErr (InternalError "Unexpected '_'"))
elaborate' FFanOut = pure $ SomeRaw' RFanOut
elaborate' FFanIn = pure $ SomeRaw' RFanIn

elabBody :: FBody -> FC -> Either Error (FunBody Raw Noun)
elabBody (FClauses cs) fc = ThunkOf . WC fc . Clauses <$> traverse elab1Clause cs
 where
  elab1Clause :: (WC Abstractor, WC Flat)
              -> Either Error (WC Abstractor, WC (Raw Chk Noun))
  elab1Clause (abs, tm) = do
    SomeRaw tm <- elaborate tm
    tm <- assertNoun tm
    tm <- assertChk tm
    pure (abs, tm)
elabBody (FNoLhs e) _ = do
    SomeRaw e <- elaborate e
    e <- assertChk e
    case kind (unWC e) of
      Nouny -> pure $ NoLhs e
      _ -> assertUVerb e >>= \e -> pure $ ThunkOf (WC (fcOf e) (NoLhs e))
elabBody FUndefined _ = pure Undefined

elabFunDecl :: FDecl -> Either Error RawFuncDecl
elabFunDecl d = do
  rc <- elabBody (fnBody d) (fnLoc d)
  pure $ FuncDecl
    { fnName = fnName d
    , fnLoc = fnLoc d
    , fnSig = fnSig d
    , fnBody = rc
    , fnLocality = fnLocality d
    }


elabEnv :: FEnv -> Either Error RawEnv
elabEnv (ds, x) = (,x,empty) <$> forM ds elabFunDecl
