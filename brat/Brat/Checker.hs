module Brat.Checker (checkBody
                    ,check
                    ,run
                    ,kindCheck
                    ,kindCheckAnnotation
                    ,kindCheckRow
                    ,tensor
                    ) where

import Control.Exception (assert)
import Control.Monad (foldM, forM, zipWithM_)
import Control.Monad.Freer
import Data.Bifunctor
import Data.Foldable (for_)
import Data.Functor (($>), (<&>))
import Data.List ((\\), intercalate)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as M
import Data.Maybe (fromJust)
import qualified Data.Set as S
import Data.Type.Equality ((:~:)(..))
import Prelude hiding (filter)

import Brat.Checker.Helpers
import Brat.Checker.Monad
import Brat.Checker.Quantity
import Brat.Checker.SolveHoles (typeEq)
import Brat.Checker.SolvePatterns (argProblems, argProblemsWithLeftovers, solve)
import Brat.Checker.Types
import Brat.Constructors
import Brat.Error
import Brat.Eval
import Brat.FC hiding (end)
import qualified Brat.FC as FC
import Brat.Graph
import Brat.Naming
import Brat.QualName
-- import Brat.Search
import Brat.Syntax.Abstractor (NormalisedAbstractor(..), normaliseAbstractor)
import Brat.Syntax.CircuitProperties (CircuitProperties(..), Properties)
import Brat.Syntax.Common
import Brat.Syntax.Core
import Brat.Syntax.FuncDecl (FunBody(..))
import Brat.Syntax.Port (ToEnd, toEnd)
import Brat.Syntax.Simple
import Brat.Syntax.Value
import Bwd
import Hasochism
import Util (zipSameLength)

-- Put things into a standard form in a kind-directed manner, such that it is
-- meaningful to do case analysis on them
standardise :: TypeKind -> Val Z -> Checking (Val Z)
standardise k val = eval S0 val >>= (\case
  (Nat, val) -> pure . VNum $ numVal val
  (_, val) -> pure val) . (k,)

mergeEnvs :: [Env a] -> Checking (Env a)
mergeEnvs = foldM combineDisjointEnvs M.empty
 where
  combineDisjointEnvs :: M.Map QualName v -> M.Map QualName v -> Checking (M.Map QualName v)
  combineDisjointEnvs l r =
    let commonKeys = S.intersection (M.keysSet l) (M.keysSet r)
    in if S.null commonKeys
       then pure $ M.union l r
       else typeErr ("Variable(s) defined twice: " ++
    intercalate "," (map show $ S.toList commonKeys))


singletonEnv :: (?my :: Modey m) => String -> (Src, BinderType m) -> Checking (Env (EnvData m))
singletonEnv x input@(p, ty) = case ?my of
  Braty -> pure $ M.singleton (plain x) [(p, ty)]
  Kerny -> do
    ty <- standardise (Dollar []) ty
    q <- case copyable ty of
      Just True -> pure Tons
      Just False -> pure One
      Nothing -> err $ InternalError $ "Didn't expect " ++ show ty ++ " in a kernel type"
    pure $ M.singleton (plain x) (q, input)

class TensorOutputs d where
  tensor :: d -> d -> d

instance TensorOutputs () where
  tensor () () = ()

instance TensorOutputs [(Src, KindOr a)] where
 tensor ss ts = ss <> ts

instance TensorOutputs [(Src, Val Z)] where
 tensor ss ts = ss <> ts

class CombineInputs d where
  combine :: d -> d -> d

instance CombineInputs () where
  combine () () = ()

instance CombineInputs [(Tgt, a)] where
  combine = (++)

type CheckConstraints m k =
  (Show (BinderType m)
  ,TensorOutputs (Outputs m Syn)
  ,TensorOutputs (Outputs m Chk)
  ,CombineInputs (Inputs m k)
  ,CombineInputs (Inputs m Noun)
  ,CombineInputs (Inputs m UVerb)
  ,CombineInputs (Inputs m KVerb)
  )

checkWire :: Modey m
          -> WC (Term d k) -- The term (for error reporting)
          -> Bool -- Is the "Src" node the expected one?
          -> (Src, BinderType m)
          -> (Tgt, BinderType m)
          -> Checking ()
checkWire Braty _ outputs (dangling, Left ok) (hungry, Left uk) = do
  throwLeft $ if outputs
    then kindEq ok uk
    else kindEq uk ok
  defineTgt hungry (endVal ok (ExEnd (end dangling)))
  wire (dangling, kindType ok, hungry)
checkWire Braty (WC fc tm) outputs (dangling, o) (hungry, u) = localFC fc $ do
  let ot = binderToValue Braty o
  let ut = binderToValue Braty u
  if outputs
    then typeEq (show tm) (Star []) ot ut
    else typeEq (show tm) (Star []) ut ot
  wire (dangling, ot, hungry)
checkWire Kerny (WC fc tm) outputs (dangling, ot) (hungry, ut) = localFC fc $ do
  if outputs
    then typeEq (show tm) (Dollar []) ot ut
    else typeEq (show tm) (Dollar []) ut ot
  wire (dangling, ot, hungry)

checkIO :: forall m d k exp act . (CheckConstraints m k, ?my :: Modey m)
        => WC (Term d k)
        -> [(NamedPort exp, BinderType m)]
        -> [(NamedPort act, BinderType m)]
        -> ((NamedPort exp, BinderType m) -> (NamedPort act, BinderType m) -> Checking ())
        -> String
        -> Checking [(NamedPort exp, BinderType m)] -- left(overs/unders)
checkIO tm@(WC fc _) exps acts wireFn errMsg = modily ?my $ do
  let (rows, rest) = zipSuffixes exps acts
  localFC fc $ forM rows $ \(e:|exps, a:|acts) ->
      wrapError (addRowContext (showRow $ e:exps) (showRow $ a:acts)) $ wireFn e a
  throwLeft $ first (\(b:|bs) -> TypeErr $ errMsg ++ showRow (b:bs) ++ " for " ++ show tm) rest
 where
  addRowContext :: String -> String -> Error -> Error
  addRowContext exp act = \case
    (Err fc (TypeMismatch tm _ _)) -> Err fc $ TypeMismatch tm exp act
    e -> e
  zipSuffixes :: [a] -> [b] -> ([(NonEmpty a, NonEmpty b)], Either (NonEmpty b) [a])
  zipSuffixes as [] = ([], Right as)
  zipSuffixes [] (b:bs) = ([], Left (b:|bs)) -- indicates error
  zipSuffixes (a:as) (b:bs) = first ((a:|as,b:|bs):) $ zipSuffixes as bs

checkInputs :: forall m d . (CheckConstraints m KVerb, ?my :: Modey m)
            => WC (Term d KVerb)
            -> [(Src, BinderType m)] -- Expected
            -> [(Tgt, BinderType m)] -- Actual
            -> Checking [(Src, BinderType m)]
checkInputs tm overs unders = checkIO tm overs unders (checkWire ?my tm False) "No overs but unders: "

checkOutputs :: forall m k . (CheckConstraints m k, ?my :: Modey m)
             => WC (Term Syn k)
             -> [(Tgt, BinderType m)] -- Expected
             -> [(Src, BinderType m)] -- Actual
             -> Checking [(Tgt, BinderType m)]
checkOutputs tm unders overs = checkIO tm unders overs (flip $ checkWire ?my tm True) "No unders but overs: "

check :: (CheckConstraints m k
         ,EvMode m
         ,TensorOutputs (Outputs m d)
         ,?my :: Modey m
         ,?props :: Properties m
         , DIRY d)
      => WC (Term d k)
      -> ChkConnectors m d k
      -> Checking (SynConnectors m d k
                  ,ChkConnectors m d k)
check (WC fc tm) conn = localFC fc (check' tm conn)

check' :: forall m d k
        . (CheckConstraints m k
          ,EvMode m
          ,TensorOutputs (Outputs m d)
          ,?my :: Modey m
          ,?props :: Properties m
          , DIRY d)
       => Term d k
       -> ChkConnectors m d k
       -> Checking (SynConnectors m d k
                   ,ChkConnectors m d k) -- rightovers
check' Empty tys = pure (((), ()), tys)
check' (s :|: t) tys = do
  -- in Checking mode, each LHS/RHS removes its wires+types from the ChkConnectors remaining
  ((ins, outs), tys)  <- check s tys
  ((ins', outs'), tys) <- check t tys
  -- in Synthesizing mode, instead here we join together the outputs, and the inputs
  pure ((combine ins ins', tensor outs outs'), tys)
check' (s :-: t) (overs, unders) = do
  -- s is Syn, t is a UVerb
  ((ins, overs), (rightovers, ())) <- check s (overs, ())
  (((), outs), (emptyOvers, rightunders)) <- check t (overs, unders)
  ensureEmpty "composition overs" emptyOvers
  pure ((ins, outs), (rightovers, rightunders))
check' Pass ([], ()) = typeErr "pass is being given an empty row"
check' Pass (overs, ()) = pure (((), overs), ([], ()))
check' (Lambda c@(WC abstFC abst,  body) cs) (overs, unders) = do
  -- Used overs have their port pulling taken care of
  (problem, rightOverSrcs) <- localFC abstFC $ argProblemsWithLeftovers (fst <$> overs) (normaliseAbstractor abst) []
  -- That processes the whole abstractor, so all of the overs in the
  -- `Problem` it creates are used
  let usedOvers = [ (src, fromJust (lookup src overs)) | (src, _) <- problem ]
  let rightOvers = [ over | over@(src,_) <- overs, src `elem` rightOverSrcs ]
  case diry @d of
    Chky -> do
      -- We'll check the first variant against a Hypo node (omitted from compilation)
      -- to work out how many overs/unders it needs, and then check it again (in Chk)
      -- with the other clauses, as part of the body.
      (FunTy _ ins outs) <- mkSig usedOvers unders
      (allFakeUnders, rightFakeUnders, tgtMap) <- suppressHoles $ suppressGraph $ do
        (_, [], fakeOvers, fakeAcc) <- anext "lambda_fake_source" Hypo (S0, Some (Zy :* S0)) R0 ins
        -- Hypo `check` calls need an environment, even just to compute leftovers;
        -- we get that env by solving `problem` reformulated in terms of the `fakeOvers`
        let srcMap = fromJust $ zipSameLength (fst <$> usedOvers) (fst <$> fakeOvers)
        let fakeProblem = [ (fromJust (lookup src srcMap), pat) | (src, pat) <- problem ]
        fakeEnv <- localFC abstFC $ solve ?my fakeProblem >>= (solToEnv . snd)
        localEnv fakeEnv $ do
          (_, fakeUnders, [], _) <- anext "lambda_fake_target" Hypo fakeAcc outs R0
          Just tgtMap <- pure $ zipSameLength (fst <$> fakeUnders) unders
          (((), ()), ((), rightFakeUnders)) <- check body ((), fakeUnders)
          pure (fakeUnders, rightFakeUnders, tgtMap)

      let usedFakeUnders = (fst <$> allFakeUnders) \\ (fst <$> rightFakeUnders)
      let usedUnders = [ fromJust (lookup tgt tgtMap) | tgt <- usedFakeUnders ]
      let rightUnders = [ fromJust (lookup tgt tgtMap) | (tgt, _) <- rightFakeUnders ]
      sig <- mkSig usedOvers usedUnders
      patOuts <- checkClauses sig usedOvers (c :| cs)
      mkWires patOuts usedUnders
      pure (((), ()), (rightOvers, rightUnders))
    Syny -> do
      synthOuts <- suppressHoles $ suppressGraph $ do
        env <- localFC abstFC $
          argProblems (fst <$> usedOvers) (normaliseAbstractor abst) [] >>=
          solve ?my >>=
          (solToEnv . snd)
        (((), synthOuts), ((), ())) <- localEnv env $ check body ((), ())
        pure synthOuts

      sig <- mkSig usedOvers synthOuts
      patOuts <- checkClauses sig usedOvers ((fst c, WC (fcOf body) (Emb body)) :| cs)
      pure (((), patOuts), (rightOvers, ()))
 where
  -- Invariant: When solToEnv is called, port pulling has already been resolved,
  -- because that's one of the functions of `argProblems`.
  --
  -- N.B.: Here we update the port names to be the user variable names for nicer
  -- error messages. This mirrors previous behaviour using `abstract`, but is a
  --  bit of a hack. See issue #23.
  solToEnv :: [(String, (Src, BinderType m))] -> Checking (M.Map QualName (EnvData m))
  solToEnv xs = traverse (uncurry singletonEnv) (portNamesToBoundNames xs) >>= mergeEnvs

  portNamesToBoundNames :: [(String, (Src, BinderType m))] -> [(String, (Src, BinderType m))]
  portNamesToBoundNames = fmap (\(n, (src, ty)) -> (n, (NamedPort (end src) n, ty)))

  mkSig :: ToEnd t => [(Src, BinderType m)] -> [(NamedPort t, BinderType m)] -> Checking (FunTy m Z)
  mkSig overs unders = rowToRo ?my (retuple <$> overs) S0 >>=
    \(Some (inRo :* endz)) -> rowToRo ?my (retuple <$> unders) endz >>=
      \(Some (outRo :* _)) -> pure (FunTy ?props inRo outRo)


  retuple (NamedPort e p, ty) = (p, e, ty)

  mkWires overs unders = case zipSameLength overs unders of
    Nothing -> err $ InternalError "Trying to wire up different sized lists of wires"
    Just conns -> traverse (\((src, ty), (tgt, _)) -> wire (src, binderToValue ?my ty, tgt)) conns

  checkClauses cty@(FunTy _ ins outs) overs all_cs = do
    let clauses = NE.zip (NE.fromList [0..]) all_cs <&>
            \(i, (abs, tm)) -> Clause i (normaliseAbstractor <$> abs) tm
    clauses <- traverse (checkClause ?my "lambda" cty) clauses
    (_, patMatchUnders, patMatchOvers, _) <- anext "lambda" (PatternMatch clauses) (S0, Some (Zy :* S0))
                                             ins
                                             outs
    mkWires overs patMatchUnders
    pure patMatchOvers

check' (Pull ports t) (overs, unders) = do
  unders <- pullPortsRow ports unders
  check t (overs, unders)
check' (t ::: outs) (overs, ()) | Braty <- ?my = do
  (ins :->> outs) :: FunTy Brat Z <- kindCheckAnnotation Braty () ":::" outs
  (_, hungries, danglies, _) <- next "id" Id (S0,Some (Zy :* S0)) ins outs
  ((), leftOvers) <- noUnders $ check t (overs, hungries)
  pure (((), danglies), (leftOvers, ()))
check' (Emb t) (overs, unders) = do
  ((ins, outs), (overs, ())) <- check t (overs, ())
  unders <- checkOutputs t unders outs
  pure ((ins, ()), (overs, unders))
check' (Th tm) ((), u@(hungry, ty):unders) = case (?my, ty) of
  (Braty, ty) -> do
    ty <- evalBinder Braty ty
    case ty of
      -- the case split here is so we can be sure we have the necessary CheckConstraints
      Right ty@(VFun Braty cty) -> checkThunk Braty "thunk" cty tm >>= wire . (,ty, hungry)
      Right ty@(VFun Kerny cty) -> checkThunk Kerny "thunk" cty tm >>= wire . (,ty, hungry)
      Left (Star args) -> kindCheck [(hungry, Star args)] (Th tm) $> ()
      _ -> err . ExpectedThunk "" $ showRow (u:unders)
    pure (((), ()), ((), unders))
  (Kerny, _) -> err . ThunkInKernel $ show (Th tm)
 where
  checkThunk :: forall m. (CheckConstraints m UVerb, EvMode m)
           => Modey m
           -> String
           -> FunTy m Z
           -> WC (Term Chk UVerb)
           -> Checking Src
  checkThunk m name cty@(FunTy props _ _) tm = do
    ((dangling, _), ()) <- let ?my = m in makeBox name cty $
      \(thOvers, thUnders) -> do
        (((), ()), leftovers) <- let ?props = props in check tm (thOvers, thUnders)
        case leftovers of
          ([], []) -> pure ()
          ([], unders) -> err (ThunkLeftUnders (showRow unders))
          -- If there are leftovers and leftunders, complain about the leftovers
          -- Until we can report multiple errors!
          (overs, _) -> err (ThunkLeftOvers (showRow overs))
    pure dangling
check' (TypedTh t) ((), ()) = case ?my of
  -- the thunk itself must be Braty
  Kerny -> err . ThunkInKernel $ show (TypedTh t)
  Braty -> do
    -- but the computation in it could be either Brat or Kern
    brat <- catchErr $ check t ((), ())
    -- TODO: What if the programmer intends a less strict kernel type?
    let props = PControllable
    kern <- catchErr $ let ?my = Kerny in let ?props = props in check t ((), ())
    case (brat, kern) of
      (Left e, Left _) -> req $ Throw e -- pick an error arbitrarily
      -- I don't believe that there is any syntax that could synthesize
      -- both a classical type and a kernel type, but just in case:
      -- (pushing down Emb(TypedTh(v)) to Thunk(Emb+Forget(v)) would help in Checkable cases)
      (Right _, Right _) -> typeErr "TypedTh could be either Brat or Kernel"
      (Left _, Right (conns, ((), ()))) -> let ?my = Kerny in createThunk props conns
      (Right (conns, ((), ())), Left _) -> createThunk () conns
 where
  createThunk :: (CheckConstraints m2 Noun, ?my :: Modey m2, EvMode m2)
              => Properties m2
              -> SynConnectors m2 Syn KVerb
              -> Checking (SynConnectors Brat Syn Noun
                          ,ChkConnectors Brat Syn Noun)
  createThunk ps (ins, outs) = do
    Some (ez :* inR) <- mkArgRo ?my S0 (first (fmap toEnd) <$> ins)
    Some (_ :* outR) <- mkArgRo ?my ez (first (fmap toEnd) <$> outs)
    (thunkOut, ()) <- makeBox "thunk" (FunTy ps inR outR) $
        \(thOvers, thUnders) -> do
          -- if these ensureEmpty's fail then its a bug!
          checkInputs t thOvers ins >>= ensureEmpty "TypedTh inputs"
          checkOutputs t thUnders outs >>= ensureEmpty "TypedTh outputs"
    pure (((), [thunkOut]), ((), ()))
check' (Force th) ((), ()) = do
  (((), outs), ((), ())) <- let ?my = Braty in let ?props = () in check th ((), ())
  -- pull a bunch of thunks (only!) out of here
  (_, thInputs, thOutputs) <- getThunks ?my ?props outs
  pure ((thInputs, thOutputs), ((), ()))

check' (Forget kv) (overs, unders) = do
  ((ins, outs), ((), rightUnders)) <- check kv ((), unders)
  leftOvers <- checkInputs kv overs ins
  pure (((), outs), (leftOvers, rightUnders))
check' (Var x) ((), ()) = (, ((), ())) . ((),) <$> case ?my of
  Braty -> vlup x
  Kerny -> req (KLup x) >>= \case
    Just (p, ty) -> pure [(p, ty)]
    Nothing -> err $ KVarNotFound (show x)
check' (Arith op l r) ((), u@(hungry, ty):unders) = case (?my, ty) of
  (Braty, ty) -> do
    ty <- evalBinder Braty ty
    case ty of
      Right TNat -> check_arith TNat
      Right TInt -> check_arith TInt
      Right TFloat -> check_arith TFloat
      _ -> err . ArithNotExpected $ show u
    pure (((), ()), ((), unders))
  (Kerny, _) -> err ArithInKernel
 where
  check_arith ty = let ?my = Braty in do
    let inRo = RPr ("left", ty) $ RPr ("right", ty) R0
    let outRo = RPr ("out", ty) R0
    (_, [lunders, runders], [(dangling, _)], _) <- next (show op) (ArithNode op) (S0, Some $ Zy :* S0) inRo outRo
    (((), ()), ((), leftUnders)) <- let ?props = () in check l ((), [lunders])
    ensureEmpty "arith unders" leftUnders
    (((), ()), ((), leftUnders)) <- let ?props = () in check r ((), [runders])
    ensureEmpty "arith unders" leftUnders
    wire (dangling, ty, hungry)
    pure (((), ()), ((), unders))
check' (fun :$: arg) (overs, unders) = do
  ((ins, outputs), ((), leftUnders)) <- check fun ((), unders)
  ((argIns, ()), (leftOvers, argUnders)) <- check arg (overs, ins)
  if null argUnders
  then pure ((argIns, outputs), (leftOvers, leftUnders))
  else typeErr $ unwords ["Expected function", show fun
                         ,"to consume all of its arguments (" ++ show arg ++ ")\n"
                         ,"but found leftovers:", showRow argUnders
                         ]
check' (Let abs x y) conn = do
  (((), dangling), ((), ())) <- check x ((), ())
  env <- abstractAll dangling (unWC abs)
  localEnv env $ check y conn
check' (NHole (mnemonic, name)) connectors = do
  fc <- req AskFC
  let suggestions = Nothing
  () <- case ?my of
    Kerny -> req $ LogHole $ TypedHole NKHole (HoleData { .. })
    Braty -> req $ LogHole $ TypedHole NBHole (HoleData { .. })
  pure (((), ()), ((), []))
-- TODO: Fix this
{-
  where
   getSuggestions :: FC -> Checking [String]
    do
      matches <- findMatchingNouns
      let sugg = transpose [ [ tm | tm <- vsearch fc ty ]
                           | (_, ty) <- unders]
      let ms = intercalate ", " . fmap show <$> matches
      let ss = intercalate ", " . fmap show <$> sugg
      pure $ take 5 (ms ++ ss)

    findMatchingNouns :: Checking [[QualName]]
    findMatchingNouns = do
      -- TODO
      pure []

      let tys = snd <$> unders
      env <- req AskVEnv
      let matches = transpose $
            [ [ (nm, src) | (src, _) <- stuff ]
            | (nm, stuff) <- M.assocs env
            , and (zipWith (==) tys (snd <$> stuff))
            ]
      pure $ fmap fst <$> matches
-}

check' (VHole (mnemonic, name)) connectors = do
  fc <- req AskFC
  let suggestions = Nothing
  req $ LogHole $ case ?my of
    Braty -> TypedHole VBHole (HoleData { .. })
    Kerny -> TypedHole VKHole (HoleData { .. })
  pure (((), ()), ([], []))
-- TODO: Better error message
check' tm@(Con _ _) ((), []) = typeErr $ "No type to check " ++ show tm ++ " against"
check' tm@(Con vcon vargs) ((), (hungry, ty):unders) = case (?my, ty) of
  (Braty, Left k) -> do
    (_, leftOvers) <- kindCheck [(hungry, k)] (Con vcon vargs)
    ensureEmpty "kindCheck leftovers" leftOvers
    pure (((), ()), ((), unders))
  (Braty, Right ty) -> aux Braty clup ty $> (((), ()), ((), unders))
  (Kerny, _) -> aux Kerny kclup ty $> (((), ()), ((), unders))
 where
  aux :: Modey m -> (QualName -> QualName -> Checking (CtorArgs m)) -> Val Z -> Checking ()
  aux my lup ty = do
    VCon tycon tyargs <- eval S0 ty
    (CArgs pats nFree _ argTypeRo) <- lup vcon tycon
    -- Look for vectors to produce better error messages for mismatched lengths
    wrap <- detectVecErrors vcon tycon tyargs pats ty (Left tm)
    Some (ny :* env) <- throwLeft $ valMatches tyargs pats
    -- Make sure env is the correct length for args
    Refl <- throwLeft $ natEqOrBust ny nFree
    let topy = roTopM my ny argTypeRo
    -- Weaken the scope of ty from Z to the top end of argTypeRo
    -- in the kernel case the bottom and top of the row are the same
    let ty' = weaken topy ty
    env <- traverseStack (sem S0) env
    (_, argUnders, [(dangling, _)], _) <- anext (show vcon) (Constructor vcon)
                                          (env, Some (Zy :* S0))
                                          argTypeRo (RPr ("value", ty') R0)
    (((), ()), ((), leftUnders)) <- wrapError wrap $ check vargs ((), argUnders)
    ensureEmpty "con unders" leftUnders
    wire (dangling, ty, hungry)

check' (C cty) ((), (hungry, ty):unders) = case (?my, ty) of
  (Braty, Left k) -> do
    (_, leftOvers) <- kindCheck [(hungry, k)] (C cty)
    ensureEmpty "kindCheck leftovers" leftOvers
    pure (((), ()), ((), unders))
  _ -> typeErr $ "Ill-kinded function type: " ++ show cty
check' (Simple tm) ((), (hungry, ty):unders) = do
  ty <- evalBinder ?my ty
  case (?my, ty, tm) of
    -- The only SimpleType that checks against a kind is a Nat
    (Braty, Left Nat, Num n) -> do
      (_, _, [(dangling, _)], _) <- next "const" (Const (Num n)) (S0,Some (Zy :* S0))
                                    R0 (REx ("value", Nat) R0)
      let val = VNum (nConstant (fromIntegral n))
      defineSrc dangling val
      defineTgt hungry val
      wire (dangling, kindType Nat, hungry)
      pure (((), ()), ((), unders))
    -- No defining needed, so everything else can be unified
    _ -> do
      let vty = biType @m ty
      throwLeft $ simpleCheck ?my vty tm
      (_, _, [(dangling, _)], _) <- anext @m "const" (Const tm) (S0,Some (Zy :* S0))
                                     R0 (RPr ("value", vty) R0)
      wire (dangling, vty, hungry)
      pure (((), ()), ((), unders))
check' FanOut ((p, ty):overs, ()) = do
  ty <- eval S0 (binderToValue ?my ty)
  case ty of
    TVec elTy n
      | VNum n <- n
      , Just n <- numValIsConstant n ->
          if n < 0
          then err (InternalError $ "Vector of negative length (" ++ show n ++ ")")
          else do
            wires <- fanoutNodes ?my n (p, valueToBinder ?my ty) elTy
            pure (((), wires), (overs, ()))
      | otherwise -> typeErr $ "Can't fanout a Vec with non-constant length: " ++ show n
    _ -> typeErr "Fanout ([/\\]) only applies to Vec"
 where
  fanoutNodes :: Modey m -> Integer -> (Src, BinderType m) -> Val Z -> Checking [(Src, BinderType m)]
  fanoutNodes _ 0 _ _ = pure []
  fanoutNodes my n (dangling, ty) elTy = do
    (_, [(hungry, _)], [danglingHead, danglingTail], _) <- anext "fanoutNodes" (Selector (plain "cons")) (S0, Some (Zy :* S0))
      (RPr ("value", binderToValue my ty) R0)
      (RPr ("head", elTy) (RPr ("tail", TVec elTy (VNum (nConstant (n - 1)))) R0) :: Ro m Z Z)
    -- Wire the input into the selector node
    wire (dangling, binderToValue my ty, hungry)
    (danglingHead:) <$> fanoutNodes my (n - 1) danglingTail elTy

check' FanIn (overs, (tgt, ty):unders) = do
  ty <- eval S0 (binderToValue ?my ty)
  case ty of
    TVec elTy n
      | VNum n <- n
      , Just n <- numValIsConstant n ->
          if n < 0
          then err (InternalError $ "Vector of negative length (" ++ show n ++ ")")
          else faninNodes ?my n (tgt, valueToBinder ?my ty) elTy overs >>= \case
            Just overs -> pure (((), ()), (overs, unders))
            Nothing -> typeErr ("Not enough inputs to make a vector of size " ++ show n)
      | otherwise -> typeErr $ "Can't fanout a Vec with non-constant length: " ++ show n
    _ -> typeErr "Fanin ([\\/]) only applies to Vec"
 where
  faninNodes :: Modey m
             -> Integer             -- The number of things left to pack up
             -> (Tgt, BinderType m) -- The place to wire the resulting vector to
             -> Val Z               -- Element type
             -> [(Src, BinderType m)] -- Overs
             -> Checking (Maybe [(Src, BinderType m)]) -- Leftovers
  faninNodes my 0 (tgt, ty) elTy overs = do
    (_, _, [(dangling, _)], _) <- anext "nil" (Constructor (plain "nil")) (S0, Some (Zy :* S0))
                             (R0 :: Ro m Z Z)
                             (RPr ("value", TVec elTy (VNum nZero)) R0)
    wire (dangling, binderToValue my ty, tgt)
    pure (Just overs)
  faninNodes _ _ _ _ [] = pure Nothing
  faninNodes my n (hungry, ty) elTy ((over, overTy):overs) = do
    let k = case my of
          Kerny -> Dollar []
          Braty -> Star []
    typeEq (show FanIn) k elTy (binderToValue my overTy)
    let tailTy = TVec elTy (VNum (nConstant (n - 1)))
    (_, [(hungryHead, _), (hungryTail, tailTy)], [(danglingResult, _)], _) <- anext "faninNodes" (Constructor (plain "cons")) (S0, Some (Zy :* S0))
      (RPr ("head", elTy) (RPr ("tail", tailTy) R0) :: Ro m Z Z)
      (RPr ("value", binderToValue my ty) R0)
    wire (over, elTy, hungryHead)
    wire (danglingResult, binderToValue ?my ty, hungry)
    faninNodes my (n - 1) (hungryTail, tailTy) elTy overs
check' Identity (this:leftovers, ()) = pure (((), [this]), (leftovers, ()))
check' (Of n e) ((), unders) = case ?my of
  Kerny -> typeErr "`of` not supported in kernel contexts"
  Braty -> do
    -- TODO: Our expectations about Id nodes in compilation might need updated?
    (_, [(natUnder,Left k)], [(natOver, _)], _) <- anext "Of_len" Id (S0, Some (Zy :* S0))
                                                   (REx ("value", Nat) R0)
                                                   (REx ("value", Nat) R0)
    ([n], leftovers) <- kindCheck [(natUnder, k)] (unWC n)
    defineSrc natOver n
    ensureEmpty "" leftovers
    case diry @d of
      -- Get the largest prefix of unders whose types are vectors of the right length
      Chky -> getVecs n unders >>= \case
        -- If none of the unders have the right type, we should fail
        ([], [], _) -> let expected = if null unders then "empty row" else showRow unders in
                        typeErr $ unlines ["Got: Vector of length " ++ show n
                                          ,"Expected: " ++ expected]
        (elemUnders, vecUnders, rightUnders) -> do
          (Some (_ :* stk)) <- rowToRo ?my [ (portName tgt, tgt, Right ty) | (tgt, ty) <- elemUnders ] S0
          case stk of
            S0 -> do
              (repConns, tgtMap) <- mkReplicateNodes n elemUnders
              let (lenIns, repUnders, repOvers) = unzip3 repConns
              -- Wire the length into all the replicate nodes
              for_ lenIns $ \(tgt, _) -> do
                wire (natOver, kindType Nat, tgt)
                defineTgt tgt n
              (((), ()), ((), elemRightUnders)) <- check e ((), repUnders)
              -- If `elemRightUnders` isn't empty, it means we were too greedy
              -- in the call to getVecs, so we should work out which elements of
              -- the original unders weren't used, and make sure they prefix the
              -- unders returned from here.
              let unusedVecTgts :: [Tgt] = fromJust . flip lookup tgtMap . fst <$> elemRightUnders
              let (usedVecUnders, unusedVecUnders) = splitAt (length vecUnders - length unusedVecTgts) vecUnders
              -- Wire up the outputs of the replicate nodes to the _used_ vec
              -- unders. The remainder of the replicate nodes don't get used.
              -- (their inputs live in `elemRightUnders`)
              assert (length repOvers >= length usedVecUnders) $ do
                zipWithM_ (\(dangling, _) (hungry, ty) -> wire (dangling, ty, hungry)) repOvers usedVecUnders
                pure (((), ()), ((), (second Right <$> unusedVecUnders) ++ rightUnders))

            _ -> localFC (fcOf e) $ typeErr "No type dependency allowed when using `of`"
      Syny -> do
        (((), outputs), ((), ())) <- check e ((), ())
        Some (_ :* stk) <- rowToRo ?my [(portName src, src, ty) | (src, ty) <- outputs] S0
        case stk of
          S0 -> do
            -- Use of `outputs` and the map returned here are nonsensical, but we're
            -- ignoring the map anyway
            outputs <- getVals outputs
            (conns, _) <- mkReplicateNodes n outputs
            let (lenIns, elemIns, vecOuts) = unzip3 conns
            for_ lenIns $ \(tgt,_) -> do
              wire (natOver, kindType Nat, tgt)
              defineTgt tgt n
            zipWithM_ (\(dangling, ty) (hungry, _) -> wire (dangling, ty, hungry)) outputs elemIns
            pure (((), vecOuts), ((), ()))
          _ -> localFC (fcOf e) $ typeErr "No type dependency allowed when using `of`"
 where
  getVals :: [(t, BinderType Brat)] -> Checking [(t, Val Z)]
  getVals [] = pure []
  getVals ((t, Right ty):rest) = ((t, ty):) <$> getVals rest
  getVals ((_, Left _):_) = localFC (fcOf e) $ typeErr "No type dependency allowed when using `of`"

  mkReplicateNodes :: forall t
                    . ToEnd t
                   => Val Z
                   -> [(t, Val Z)] -- The unders from getVec, only used for building the map
                   -> Checking ([((Tgt, BinderType Brat) -- The Tgt for the vector length
                                 ,(Tgt, BinderType Brat) -- The Tgt for the element
                                 ,(Src, BinderType Brat) -- The vectorised element output
                                 )]
                               ,[(Tgt, t)] -- A map from element tgts to the original vector tgts
                               )
  mkReplicateNodes _ [] = pure ([], [])
  mkReplicateNodes len ((t, ty):unders) = do
    let weakTy = changeVar (Thinning (ThDrop ThNull)) ty
    (_, [lenUnder, repUnder], [repOver], _) <- anext "replicate" Replicate (S0, Some (Zy :* S0))
                                               (REx ("n", Nat) (RPr ("elem", weakTy) R0)) -- the type of e
                                               (RPr ("vec", TVec weakTy (VApp (VInx VZ) B0)) R0) -- a vector of e's of length n??
    (conns, tgtMap) <- mkReplicateNodes len unders
    pure ((lenUnder, repUnder, repOver):conns, (fst repUnder, t):tgtMap)

  getVecs :: Val Z -- The length of vectors we're looking for
          -> [(Tgt, BinderType Brat)]
          -> Checking ([(Tgt, Val Z)] -- element types for which we need vecs of the given length
                      ,[(Tgt, Val Z)] -- The vector type unders which we'll wire to
                      ,[(Tgt, BinderType Brat)] -- Rightunders
                      )
  getVecs len ((tgt, Right ty@(TVec el n)):unders) = eqTest "" Nat len n >>= \case
    Left _ -> pure ([], [], (tgt, Right ty):unders)
    Right () -> do
      (elems, unders, rightUnders) <- getVecs len unders
      pure ((tgt, el):elems, (tgt, ty):unders, rightUnders)
  getVecs _ unders = pure ([], [], unders)
check' Hope ((), (NamedPort hope _, ty):unders) = case (?my, ty) of
  (Braty, Left _k) -> do
    fc <- req AskFC
    req (ANewHope hope fc)
    pure (((), ()), ((), unders))
  (Braty, Right _ty) -> typeErr "Can only infer kinded things with !"
  (Kerny, _) -> typeErr "Won't infer kernel typed !"
check' tm _ = error $ "check' " ++ show tm


-- Clauses from either function definitions or case statements, as we get
-- them from the elaborator
data Clause = Clause
  { index :: Int  -- Which clause is this (in the order they're defined in source)
  , lhs :: WC NormalisedAbstractor
  , rhs :: WC (Term Chk Noun)
  }
 deriving Show

-- Return the tests that need to succeed for this clause to fire
-- (Tests are always defined on the overs of the outer box, rather than on
-- refined overs)
checkClause :: forall m. (CheckConstraints m UVerb, EvMode m) => Modey m
            -> String
            -> FunTy m Z
            -> Clause
            -> Checking
               ( TestMatchData m -- TestMatch data (LHS)
               , Name   -- Function node (RHS)
               )
checkClause my fnName cty@(FunTy props _ _) clause = modily my $ do
  let clauseName = fnName ++ "." ++ show (index clause)

  -- First, we check the patterns on the LHS. This requires some overs,
  -- so we make a box, however this box will be skipped during compilation.
  (vars, match, rhsCty) <- suppressHoles . fmap snd $
                     let ?my = my in makeBox (clauseName ++ "_setup") cty $
                     \(overs, unders) -> do
    -- Make a problem to solve based on the lhs and the overs
    problem <- argProblems (fst <$> overs) (unWC $ lhs clause) []
    (tests, sol) <- localFC (fcOf (lhs clause)) $ solve my problem
    -- The solution gives us the variables bound by the patterns.
    -- We turn them into a row
    Some (patEz :* patRo) <- mkArgRo my S0 ((\(n, (src, ty)) -> (NamedPort (toEnd src) n, ty)) <$> sol)
    -- Also make a row for the refined outputs (shifted by the pattern environment)
    Some (_ :* outRo) <- mkArgRo my patEz (first (fmap toEnd) <$> unders)
    let match = TestMatchData my $ MatchSequence overs tests (snd <$> sol)
    let vars = fst <$> sol
    pure (vars, match, FunTy props patRo outRo)

  -- Now actually make a box for the RHS and check it
  ((boxPort, _ty), _) <- let ?my = my in makeBox (clauseName ++ "_rhs") rhsCty $ \(rhsOvers, rhsUnders) -> do
    let abstractor = foldr ((:||:) . APat . Bind) AEmpty vars
    let ?my = my in do
      env <- abstractAll rhsOvers abstractor
      localEnv env $ let ?props = props in check @m (rhs clause) ((), rhsUnders)
  let NamedPort {end=Ex rhsNode _} = boxPort
  pure (match, rhsNode)

-- Top level function for type checking function definitions
-- Will make a top-level box for the function, then type check the definition
checkBody :: (CheckConstraints m UVerb, EvMode m, ?my :: Modey m)
          => String -- The function name
          -> FunBody Term UVerb
          -> FunTy m Z -- Function type
          -> Checking Src
checkBody fnName body cty@(FunTy props _ _) = do
  (tm, (absFC, tmFC)) <- case body of
    NoLhs tm -> pure (tm, (fcOf tm, fcOf tm))
    Clauses (c@(abs, tm) :| cs) -> do
      fc <- req AskFC
      pure (WC fc (Lambda c cs), (fcOf abs, fcOf tm))
    Undefined -> err (InternalError "Checking undefined clause")
  ((src, _), _) <- makeBox (fnName ++ ".box") cty $ \conns@(_, unders) -> do
    (((), ()), leftovers) <- let ?props = props in check tm conns
    case leftovers of
      ([], []) -> pure ()
      ([], rightUnders) -> localFC tmFC $
        let numUsed = length unders - length rightUnders
        in err (TypeMismatch (show tm) (showRow unders) (showRow (take numUsed unders)))
      (rightOvers, _) -> localFC absFC $
        typeErr ("Inputs " ++ showRow rightOvers ++ " weren't used")
  pure src

-- Constructs row from a list of ends and types. Uses standardize to ensure that dependency is
-- detected. Fills in the first bot ends from a stack. The stack grows every time we go under
-- a binder. The final stack is returned, so we can compute an output row after an input row.
mkArgRo :: Modey m -> Stack Z End bot -> [(NamedPort End, BinderType m)] -> Checking (Some (Stack Z End :* Ro m bot))
mkArgRo _ ez [] = pure $ Some (ez :* R0)
mkArgRo Braty ez ((p, Left k):rest) = mkArgRo Braty (ez :<< end p) rest >>= \case
  Some (ez' :* ro) -> pure $ Some $ ez' :* REx (portName p, k) ro
mkArgRo Braty ez ((p, Right t):rest) = mkArgRo Braty ez rest >>= \case
  Some (ez' :* ro) -> do
    t <- standardise (TypeFor Brat []) t
    pure $ Some $ ez' :* RPr (portName p, abstractEndz ez t) ro
mkArgRo Kerny ez ((p, t):rest) = mkArgRo Kerny ez rest >>= \case
  Some (ez' :* ro) -> do
    t <- standardise (TypeFor Brat []) t
    pure $ Some $ ez' :* RPr (portName p, abstractEndz ez t) ro

mkKindRo :: [(PortName, TypeKind)] -> Some (Ro Brat bot)
mkKindRo [] = Some R0
mkKindRo ((p,k):rest) = case mkKindRo rest of
  Some ro -> Some $ REx (p,k) ro

-- Check a type against a row of kinds, and evaluate it
-- define the ends from unders when appropriate
-- N.B. Wires should be declared before they arrive here, we're going to define them here
kindCheck :: [(Tgt, TypeKind)] -- Kinds checking against
          -> Term Chk Noun     -- The type to scrutinise
          -> Checking ([Val Z] -- The values produced by evaluating term arguments
                      ,[(Tgt, TypeKind)]) -- Leftovers (rightunders)
kindCheck unders Empty = pure ([], unders)
kindCheck [] tm = err $ InternalError $  "kindCheck called with empty unders for " ++ show tm
kindCheck unders (a :|: b) = do
  (vs, unders) <- kindCheck unders (unWC a)
  (vs', unders) <- kindCheck unders (unWC b)
  pure (vs <> vs', unders)
kindCheck _ (Pull _ _) = err $ Unimplemented "Port pulling in kinds" [] -- FIXME
kindCheck ((hungry, k@(TypeFor m [])):unders) (Con c arg) = req (TLup (m, c)) >>= \case
  -- This must be either a type constructor...
  Just args -> case mkKindRo args of
    Some args -> do
      (_, argUnders, [(dangling, _)], _) <- next (show c) (Constructor c) (S0, Some (Zy :* S0))
                                              args --[(p, Left k) | (p, k) <- args])
                                              (REx ("value", TypeFor m []) R0)
      let kindArgs = [ (tgt, k) | (tgt, Left k) <- argUnders ]
      -- recurse first so we Define the necessary argUnders
      (_, emptyUnders) <- kindCheck kindArgs (unWC arg)
      ensureEmpty "kindCheck unders" emptyUnders
      -- now evVa can pick up the definitions
      value <- eval S0 $ VCon c [ endVal k (InEnd (end tgt)) | (tgt, k) <- kindArgs ]
      defineTgt hungry value
      defineSrc dangling value
      wire (dangling, kindType k, hungry)
      pure ([value],unders)
  -- ... or a type alias
  -- (only allow aliases to be of kind `Star`)
  Nothing | m == Brat -> req (ALup c) >>= \case
    Just (aliasArgs, aliasLam) -> case mkKindRo aliasArgs of
      Some aliasArgs -> do
        -- It only looks weird that we don't use this `va`
        -- va = endVal of (end kindOut), so not as useful as
        -- the thing we *do* define kindOut as

        (_, argUnders, [(kindOut,_)], (_ :<< _va, _)) <-
          next "kc_alias" Hypo (S0, Some (Zy :* S0)) aliasArgs (REx ("type",Star []) R0)
        -- arg is a juxtaposition
        (args, emptyUnders) <- kindCheck (second (\(Left k) -> k) <$> argUnders) (unWC arg)
        ensureEmpty "alias args" emptyUnders
        val <- apply aliasLam args
        defineSrc kindOut val
        defineTgt hungry val
        wire (kindOut, kindType k, hungry)
        pure ([val], unders)
    Nothing -> typeErr $ "Can't find type constructor or type alias " ++ show c
  Nothing -> typeErr $ "Can't find type constructor " ++ show c ++ " in this context"
kindCheck ((hungry, Star []):unders) (C (ss :-> ts)) = do
  name <- req (Fresh "__kcc")
  kindCheckRow' Braty (Zy :* S0) M.empty (name,0) ss >>= \case
    (i, env, Some (ez :* inRo)) -> kindCheckRow' Braty ez env (name, i) ts >>= \case
      (_, _, Some (_ :* outRo)) -> do
        let val = VFun Braty (inRo :->> outRo)
        defineTgt hungry val
        pure ([val], unders)
kindCheck ((hungry, Star []):unders) (K ps (ss :-> ts)) = do
  -- N.B. Kernels can't bind so we don't need to pass around a stack of ends
  ss <- kindCheckRow Kerny "" ss
  ts <- kindCheckRow Kerny "" ts
  case (ss, ts) of
    (Some ss, Some ts) -> case kernelNoBind ss of
      Refl -> do
        let val = VFun Kerny (FunTy ps ss ts)
        defineTgt hungry val
        pure ([val], unders)

-- N.B. This code is currently only called for checking the validity of type aliases
--
-- Check a lambda as the body of a higher-order kind
-- Body will contain Core.Var for things that correspond to variables bound by xs
kindCheck ((hungry, TypeFor m args):unders) (Th (WC _ (Lambda (xs, WC fc body) []))) = case mkKindRo args of
  Some ro -> do
    -- Make some ends (outputs here) to correspond to hypothetical arguments to the alias
    (_, [], kovers, (_, endz)) <- next "aliargs" Hypo (S0, Some (Zy :* S0)) R0 ro
    ext <- let ?my = Braty in abstractAll kovers (unWC xs)
    -- kindCheck the alias with those arguments into a second Hypo node
    (_, [(p, Left k)], _, _) <- next "alias" Hypo (S0, Some (Zy :* S0))
                                   (REx ("type", TypeFor m []) R0) R0
    ([vbody], emptyUnders) <- localFC fc $ localVEnv ext $ kindCheck [(p, k)] body
    ensureEmpty "kindCheck unders" emptyUnders
    vbody <- eval S0 vbody
    let vlam = case endz of
          Some (ny :* endz) -> lambdify endz (changeVar (ParToInx (AddZ ny) endz) vbody)
    defineTgt hungry vlam
    pure ([vlam], unders)
 where
  lambdify :: Stack Z End i -> Val i -> Val Z
  lambdify S0 v = v
  lambdify (zx :<< _) v = lambdify zx (VLam v)
kindCheck unders (Emb (WC fc (Var v))) = localFC fc $ vlup v >>= f unders
 where
  f :: [(Tgt, TypeKind)]
    -> [(Src, BinderType Brat)]
    -> Checking ([Val Z], [(Tgt, TypeKind)])
  f unders [] = pure ([], unders)
  f [] _ = typeErr "Empty unders"
  f  ((hungry, k'):us) ((dangling, Left k):xs) = do
    throwLeft $ kindEq k k'
    wire (dangling, kindType k, hungry)
    value <- eval S0 (endVal k (ExEnd (end dangling)))
    defineTgt hungry value
    (vs, leftUnders) <- f us xs
    pure (value:vs, leftUnders)
  f _ (x:_) = err $ InternalError $ "Kindchecking a row which contains " ++ show x
-- TODO: Add other operations on numbers
kindCheck ((hungry, Nat):unders) (Simple (Num n)) | n >= 0 = do
  (_, _, [(dangling, _)], _) <- next "const" (Const (Num n)) (S0,Some (Zy :* S0)) R0 (REx ("value", Nat) R0)
  let value = VNum (nConstant (fromIntegral n))
  defineTgt hungry value
  defineSrc dangling value
  wire (dangling, TNat, hungry)
  pure ([value], unders)
kindCheck ((hungry, Nat):unders) (Arith op lhs rhs) = do
  (_, arithUnders, [(dangling,_)], _) <- next ("arith_" ++ show op) (ArithNode op) (S0, Some (Zy :* S0))
                                         (REx ("lhs", Nat) (REx ("rhs", Nat) R0))
                                         (REx ("value", Nat) R0)
  ([vlhs, vrhs], []) <- kindCheck [ (p, k) | (p, Left k) <- arithUnders ] (lhs :|: rhs)
  let arithFC = FC (FC.start (fcOf lhs)) (FC.end (fcOf rhs))
  localFC arithFC $ case (vlhs, vrhs) of
    (VNum lhs, VNum rhs) -> do
      case runArith lhs op rhs of
        Nothing -> typeErr "Type level arithmetic too confusing"
        Just result -> do
          defineTgt hungry (VNum result)
          defineSrc dangling (VNum result)
          wire (dangling, kindType Nat, hungry)
          pure ([VNum result], unders)
    (VNum _, x) -> localFC (fcOf rhs) . typeErr $ "Expected numeric expression, found " ++ show x
    (x, VNum _) -> localFC (fcOf lhs) . typeErr $ "Expected numeric expression, found " ++ show x
    _ -> typeErr "Expected arguments to arithmetic operators to have kind #"
kindCheck ((hungry, Nat):unders) (Con c arg)
 | Just (_, f) <- M.lookup c natConstructors = do
     -- All nat constructors have one input and one output
     (_, [(chungry,_)], [(cdangling,_)], _) <- next (show c) (Constructor c) (S0, Some (Zy :* S0))
                                               (REx ("in", Nat) R0)
                                               (REx ("out", Nat) R0)
     wire (cdangling, TNat, hungry)
     ([VNum nv], us) <- kindCheck [(chungry, Nat)] (unWC arg)
     ensureEmpty "kindCheck unders" us
     v <- eval S0 (VNum (f nv))
     defineSrc cdangling v
     defineTgt hungry v
     pure ([v], unders)

kindCheck ((_, k):_) tm = typeErr $ "Expected " ++ show tm ++ " to have kind " ++ show k


-- Checks the kinds of the types in a dependent row
kindCheckRow :: Modey m
             -> String -- for node name
             -> [(PortName, ThunkRowType m)] -- The row to process
             -> Checking (Some (Ro m Z))
kindCheckRow my name r = do
  name <- req $ Fresh $ "__kcr_" ++ name
  kindCheckRow' my (Zy :* S0) M.empty (name, 0) r >>= \case
    (_, _, Some (_ :* flipped_ro)) -> pure $ Some flipped_ro

-- Checks that an annotation is a valid row, returning the
-- evaluation of the type of an Id node passing through such values
kindCheckAnnotation :: Modey m
                    -> Properties m
                    -> String -- for node name
                    -> [(PortName, ThunkRowType m)]
                    -> Checking (FunTy m Z)
kindCheckAnnotation my ps name outs = do
  trackM "kca"
  name <- req (Fresh $ "__kca_" ++ name)
  kindCheckRow' my (Zy :* S0) M.empty (name, 0) outs >>= \case
    (_, _, Some ((n :* s) :* ins)) ->
      -- Make a copy of ins whose free indices claim to start where the
      -- first left off. Since any references to the Ends in `s` have
      -- already been converted to (bound) Inx's, this does nothing,
      -- but persuades the Haskell typechecker it's ok to use the copy
      -- as return types (that happen not to mention the argument types).
      case varChangerThroughRo (ParToInx (AddZ n) s) ins of
        Some (_ :* outs) -> pure (FunTy ps ins outs)

kindCheckRow' :: forall m n
               . Modey m
              -> Endz n -- kind outports so far
              -> VEnv -- from string variable names to VPar's
              -> (Name, Int) -- node name and next free input (under to 'kindCheck' a type)
              -> [(PortName, ThunkRowType m)]
              -> Checking (Int, VEnv, Some (Endz :* Ro m n))
kindCheckRow' _ ez env (_,i) [] = pure (i, env, Some (ez :* R0))
kindCheckRow' Braty (ny :* s) env (name,i) ((p, Left k):rest) = do -- s is Stack Z n
  let dangling = Ex name (ny2int ny)
  req (Declare (ExEnd dangling) Braty (Left k))
  env <- pure $ M.insert (plain p) [(NamedPort dangling p, Left k)] env
  (i, env, ser) <- kindCheckRow' Braty (Sy ny :* (s :<< ExEnd dangling)) env (name, i) rest
  case ser of
    Some (s_m :* ro) -> pure (i, env, Some (s_m :* REx (p,k) ro))
kindCheckRow' my ez@(ny :* s) env (name, i) ((p, bty):rest) = case (my, bty) of
  (Braty, Right ty) -> helper ty (Star [])
  (Kerny, ty) -> helper ty (Dollar [])

 where
  helper :: Term Chk Noun -> TypeKind -> Checking (Int, VEnv, Some (Endz :* Ro m n))
  helper ty kind = do
    let hungry = NamedPort (In name i) p -- or always call it "type"?
    declareTgt hungry Braty (Left kind)
    ([v], []) <- localVEnv env $ kindCheck [(hungry, kind)] ty -- TODO give proper errors on failed match
    -- v has no dangling Inx's but contains Par's in `s`. Convert to `n` Inx's
    v <- pure $ changeVar (ParToInx (AddZ ny) s) v
    (i, env, ser) <- kindCheckRow' my ez env (name, i+1) rest
    case ser of
      Some (s_m :* ro) -> pure (i, env, Some (s_m :* RPr (p, v) ro))

-- Look for vectors to produce better error messages for mismatched lengths
-- in terms or patterns.
detectVecErrors :: QualName  -- Term constructor name
                -> QualName  -- Type constructor name
                -> [Val Z]   -- Type arguments
                -> [ValPat]  -- Patterns the type arguments are checked against
                -> Val Z     -- Type
                -> Either (Term d k) Pattern  -- Term or pattern
                -> Checking (Error -> Error)  -- Returns error wrapper to use for recursion
detectVecErrors vcon (PrefixName [] "Vec") [_, VNum n] [_, VPNum p] ty tp =
  case numMatch B0 n p of
    Left (NumMatchFail _ _) -> do
      p' <- toLenConstr p
      err $ getVecErr tp (show ty) (show n) p'
    -- Even if we succed here, the error might pop up when checking the
    -- rest of the vector. We return a function here that intercepts the
    -- error and extends it to the whole vector.
    _ -> if vcon == PrefixName [] "cons"
         then do fc <- req AskFC
                 pure (consError fc tp (show ty) n)
         else pure id
 where
  -- For constructors that produce something of type Vec we should
  -- only ever get the patterns NP0 (if vcon == PrefixName [] "nil")
  -- and NP1Plus (if vcon == PrefixName [] "cons")
  toLenConstr :: NumPat -> Checking LengthConstraint
  toLenConstr NP0 = pure $ Length 0
  toLenConstr (NP1Plus _) = pure $ LongerThan 0
  toLenConstr p = err $ InternalError ("detectVecErrors: Unexpected pattern: " ++ show p)
detectVecErrors _ _ _ _ _ _ = pure id

getVecErr :: Either (Term d k) Pattern -> (String -> String -> LengthConstraint -> ErrorMsg)
getVecErr (Left tm) = VecLength (show tm)
getVecErr (Right pat) = VecPatLength (show pat)

-- Wrapper extending an error occurring on the RHS of a cons to the whole vector
consError :: Show v => FC -> Either (Term d k) Pattern -> String -> NumVal v -> Error -> Error
consError fc tp ty exp err = case (tp, msg err) of
    (Left _, VecLength _ _ _ act) -> mkVecError act
    (Right _, VecPatLength _ _ _ act) -> mkVecError act
    _ -> err
 where
  mkVecError act = Err (Just fc) $ getVecErr tp ty (show exp) ((1+) <$> act)

abstractAll :: (Show (BinderType m), EvMode m, ?my :: Modey m)
            => [(Src, BinderType m)] -> Abstractor
            -> Checking (Env (EnvData m))
abstractAll stuff binder = do
    (env, unders) <- abstract stuff binder
    ensureEmpty "unders after abstract" unders
    pure env

abstract :: forall m
          . (Show (BinderType m), ?my :: Modey m, EvMode m)
         => [(Src, BinderType m)]
         -> Abstractor
         -> Checking (Env (EnvData m) -- Local env for checking body of lambda
                     ,[(Src, BinderType m)] -- rightovers
                     )
abstract inputs AEmpty = pure (emptyEnv, inputs)
abstract inputs (x :||: y) = do
  (venv, inputs)  <- abstract inputs x
  (venv', inputs) <- abstract inputs y
  (,inputs) <$> mergeEnvs [venv, venv']
abstract inputs (APull ports abst) = do
  inputs <- pullPortsRow ports inputs
  abstract inputs abst
abstract ((src, ty):inputs) (APat p) = (,inputs) <$> abstractPattern ?my (src, ty) p
abstract [] a = err (NothingToBind (show a))

abstractPattern :: forall m
                 . (EvMode m, Show (BinderType m))
                => Modey m
                -> (Src, BinderType m)
                -> Pattern
                -> Checking (Env (EnvData m)) -- Local env for checking body of lambda
abstractPattern m (src, ty) (Bind x) = let ?my = m in singletonEnv x (src, ty)
abstractPattern Braty (_, Left Nat) (Lit tm) = throwLeft (simpleCheck Braty TNat tm) $> emptyEnv
abstractPattern Braty (_, Right ty) (Lit tm) = throwLeft (simpleCheck Braty ty tm) $> emptyEnv
abstractPattern Kerny (_, ty) (Lit tm) = throwLeft (simpleCheck Kerny ty tm) $> emptyEnv
abstractPattern Braty (dangling, Left k) pat = abstractKind k pat
 where
  abstractKind :: TypeKind -> Pattern -> Checking (Env (EnvData Brat))
  abstractKind _ (Bind x) = let ?my = Braty in singletonEnv x (dangling, Left k)
  abstractKind _ DontCare = pure emptyEnv
  abstractKind k (Lit x) = case (k, x) of
    (Nat, Num n) -> defineSrc dangling (VNum (nConstant (fromIntegral n))) $> emptyEnv
    (Star _, _) -> err MatchingOnTypes
    _ -> err (PattErr $ "Couldn't resolve pattern " ++ show pat ++ " with kind " ++ show k)
--  abstractKind Braty Nat p = abstractPattern Braty (src, Right TNat) p
  abstractKind Nat pat@(PCon c parg) = do
    case M.lookup c natConstructors of
      Just (Just p, rel) -> case numMatch B0 (nVar (VPar (ExEnd (end dangling)))) p of
        -- TODO: Make some Nat deconstructor node for the wiring here
        Right (B0 :< VNum v) -> do
          (_, [], [(newDangling, _)], _) <- next "Nat pat destructor" Hypo (S0, Some (Zy :* S0)) R0 (REx ("", Nat) R0)
          defineSrc newDangling (VNum v)
          defineSrc dangling (VNum (rel v))
          let ?my = Braty in abstractAll [(newDangling, Left Nat)] parg
        _ -> err . PattErr $ "Couldn't resolve pattern " ++ show pat ++ " with kind #"
      Just (Nothing,_) -> err (PattErr $ show pat ++ " can't be used as a pattern")
      Nothing -> err (PattErr $ "Couldn't resolve pattern " ++ show pat ++ " with kind " ++ show k)
  abstractKind k (PCon _ _) = err $ PattErr $ "No patterns for matching kind " ++ show k
abstractPattern my (dangling, bty) pat@(PCon pcon abst) = case (my, bty) of
  (Braty, Right ty) -> helper my ty (Star []) clup
  (Kerny, ty) -> helper my ty (Dollar []) kclup
 where
  helper :: Modey m
         -> Val Z
         -> TypeKind
         -> (QualName -> QualName -> Checking (CtorArgs m))
         -> Checking (Env (EnvData m))
  helper my v k lup = standardise k v >>=
                      throwLeft . unpackTypeConstructor >>=
                      abstractCon my lup

  unpackTypeConstructor :: Val Z -> Either ErrorMsg (QualName, [Val Z])
  unpackTypeConstructor (VCon tycon tyargs) = pure (tycon, tyargs)
  unpackTypeConstructor ty = Left (PattErr $ unwords ["Couldn't resolve pattern"
                                                     ,show pat
                                                     ,"with type"
                                                     ,show ty])

  abstractCon :: Modey m
              -> (QualName -> QualName -> Checking (CtorArgs m))
              -> (QualName, [Val Z])
              -> Checking (Env (EnvData m))
  abstractCon my lup (tycon, tyargs) = do
    let ty = VCon tycon tyargs
    (CArgs vps nFree _ unders) <- lup pcon tycon
    -- Look for vectors to produce better error messages for mismatched lengths
    wrap <- detectVecErrors pcon tycon tyargs vps ty (Right pat)
    Some (ny :* zv) <- throwLeft $ valMatches tyargs vps
    Refl <- throwLeft $ natEqOrBust ny nFree
    -- ty is Inx-closed, but `next` expects it to have <ny> free vars,
    -- so persuade the type system of that
    let ty' = weaken ny ty
    zv <- traverseStack (sem S0) zv
    (_, [(hungry, _)], overs, _) <- anext (show pcon) (Selector pcon) (zv, Some (Zy :* S0)) (RPr ("value", ty') R0) unders
    wire (dangling, ty, hungry)
    wrapError wrap $ let ?my = my in abstractAll overs abst
abstractPattern _ _ DontCare = pure emptyEnv

weaken :: DeBruijn v => Ny n -> v Z -> v n
weaken n = changeVar (Thinning (thEmpty n))

abstractEndz :: DeBruijn v => Stack Z End n -> v Z -> v n
abstractEndz ez = changeVar (ParToInx (AddZ (stackLen ez)) ez)

run :: VEnv
    -> Store
    -> Namespace
    -> Checking a
    -> Either Error (a, ([TypedHole], Store, Graph))
run ve initStore ns m = do
  let ctx = Ctx { globalVEnv = ve
                , store = initStore
                -- TODO: fill with default constructors
                , constructors = defaultConstructors
                , kconstructors = kernelConstructors
                , typeConstructors = defaultTypeConstructors
                , aliasTable = M.empty
                , hopes = M.empty
                }
  (a,ctx,(holes, graph)) <- handler (localNS ns m) ctx mempty
  let tyMap = typeMap $ store ctx
  -- If the `hopes` set has any remaining holes with kind Nat, we need to abort.
  -- Even though we didn't need them for typechecking problems, our runtime
  -- behaviour depends on the values of the holes, which we can't account for.
  case M.toList $ M.filterWithKey (\e _ -> isNatKinded tyMap (InEnd e)) (hopes ctx) of
    [] -> pure (a, (holes, store ctx, graph))
    -- Just use the FC of the first hole while we don't have the capacity to
    -- show multiple error locations
    hs@((_,fc):_) -> Left $ Err (Just fc) (RemainingNatHopes (show . fst <$> hs))
 where
  isNatKinded tyMap e = case tyMap M.! e of
    EndType Braty (Left Nat) -> True
    _ -> False
