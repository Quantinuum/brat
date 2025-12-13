module Brat.Checker.SolveNumbers (unifyNum) where

import Brat.Checker.Monad
import Brat.Checker.Helpers
import Brat.Syntax.Value
import Brat.Syntax.Common
import Brat.Syntax.Port
import Brat.Error
import Brat.Eval
import Brat.Graph (NodeType(..))
import Brat.Naming
import Hasochism
import Control.Monad.Freer

-- import Debug.Trace
import qualified Data.Set as S

trailM :: Applicative f => String -> f ()
trailM = const (pure ())
trail = const id
--trail = trace

-- This is currently lifted from SolvePatterns, which still imports it.
-- It is also used in SolveHoles, where it does the right mathematics
-- but the wrong wiring.

-- Solve a Nat kinded metavariable. Unlike `instantiateMeta`, this function also
-- makes the dynamic wiring for a metavariable. This only needs to happen for
-- numbers because they have nontrivial runtime behaviour.
--
-- We assume that the caller has done the occurs check and rules out trivial equations.
-- The caller also must check we have the right to solve the End
solveNumMeta :: (End -> Maybe String) -> End -> NumVal (VVar Z) -> Checking ()
solveNumMeta _ e nv | trail ("solveNumMeta " ++ show e ++ " " ++ show nv) False = undefined
solveNumMeta mine e nv = case (e, numVars nv) of
 -- Compute the thing that the rhs should be based on the src, and instantiate src to that
 (ExEnd src,  [InEnd _tgt]) -> do
   -- Compute the value of the `tgt` variable from the known `src` value by inverting nv
   tgtSrc <- invertNatVal nv
   instantiateMeta "solveNumExIn" (ExEnd src) (VNum (nVar (VPar (toEnd tgtSrc))))
   wire (NamedPort src "", TNat, tgtSrc)

 (ExEnd src, _) -> instantiateMeta "solveNumEx_" (ExEnd src) (VNum nv)

 -- Both targets, we need to create the thing that they both derive from
 (InEnd bigTgt, [InEnd weeTgt]) -> do
     (_, [(idTgt, _)], [(idSrc, _)], _) <- anext "numval id" Id (S0, Some (Zy :* S0))
                                         (REx ("n", Nat) R0) (REx ("n", Nat) R0)
     defineSrc idSrc (VNum (nVar (VPar (toEnd idTgt))))
     let nv' = fmap (const (VPar (toEnd idSrc))) nv -- weeTgt is the only thing to replace
     bigSrc <- buildNatVal nv'
     nv' <- quoteNum Zy <$> numEval S0 nv'
     instantiateMeta "solveNumInIn" (InEnd bigTgt) (VNum nv')
     wire (bigSrc, TNat, NamedPort bigTgt "")
     unifyNum mine (nVar (VPar (toEnd idSrc))) (nVar (VPar (toEnd weeTgt)))



 -- RHS is constant or Src, wire it into tgt
 (InEnd tgt,  _) -> do
   src <- buildNatVal nv
   instantiateMeta "solveNumIn_" (InEnd tgt) (VNum nv)
   wire (src, TNat, NamedPort tgt "")

unifyNum :: (End -> Maybe String) -> NumVal (VVar Z) -> NumVal (VVar Z) -> Checking ()
unifyNum mine nv0 nv1 = do
  trailM $ ("unifyNum In\n  " ++ show nv0 ++ "\n  " ++ show nv1)
  nv0 <- numEval S0 nv0
  nv1 <- numEval S0 nv1
  unifyNum' mine (quoteNum Zy nv0) (quoteNum Zy nv1)
  nv0 <- numEval S0 (quoteNum Zy nv0)
  nv1 <- numEval S0 (quoteNum Zy nv1)
  trailM $ ("unifyNum Out\n  " ++ show (quoteNum Zy nv0) ++ "\n  " ++ show (quoteNum Zy nv1))

-- Need to keep track of which way we're solving - which side is known/unknown
-- Things which are dynamically unknown must be Tgts - information flows from Srcs
-- ...But we don't need to do any wiring here, right?
unifyNum' :: (End -> Maybe String) -> NumVal (VVar Z) -> NumVal (VVar Z) -> Checking ()
unifyNum' _ a b | trail ("unifyNum'\n  " ++ show a ++ "\n  " ++ show b) False = undefined
unifyNum' mine (NumValue lup lgro) (NumValue rup rgro)
  | lup <= rup = lhsFun00 lgro (NumValue (rup - lup) rgro)
  | otherwise  = lhsFun00 rgro (NumValue (lup - rup) lgro)
 where
  lhsFun00 :: Fun00 (VVar Z) -> NumVal (VVar Z) -> Checking ()
  lhsFun00 Constant0 num = demand0 num
  -- Both sides are variables
  lhsFun00 (StrictMonoFun (StrictMono 0 (Linear v))) (NumValue 0 (StrictMonoFun (StrictMono 0 (Linear v')))) = flexFlex v v'
  -- There's just a variable on the right - move it to the left
  lhsFun00 sm (NumValue 0 (StrictMonoFun smv@(StrictMono 0 (Linear _)))) = lhsStrictMono smv (NumValue 0 sm)
  lhsFun00 (StrictMonoFun sm) num = lhsStrictMono sm num

  flexFlex :: VVar Z -> VVar Z -> Checking ()
  flexFlex v v' = case compare v v' of
    GT -> flexFlex v' v
    EQ -> pure ()
    LT -> case (v, v') of
      (VPar e@(ExEnd p), VPar e'@(ExEnd p'))
       | Just _ <- mine e -> defineSrc (NamedPort p "") (VNum (nVar v'))
       | Just _ <- mine e' -> defineSrc (NamedPort p' "") (VNum (nVar v))
       | otherwise -> typeErr $ "Can't force " ++ show v ++ " to be " ++ show v'
      (VPar e@(InEnd p), VPar e'@(ExEnd dangling))
       | Just _ <- mine e -> do
          req (Wire (dangling, TNat, p))
          defineTgt' ("flex-flex In Ex") (NamedPort p "") (VNum (nVar v'))
       | Just _ <- mine e' -> do
          req (Wire (dangling, TNat, p))
          defineSrc' ("flex-flex In Ex") (NamedPort dangling "") (VNum (nVar v))
       | otherwise -> mkYield "flexFlex" (S.singleton e) >> unifyNum mine (nVar v) (nVar v')
      (VPar e@(InEnd p), VPar e'@(InEnd p'))
       | Just _ <- mine e -> defineTgt' "flex-flex In In1" (NamedPort p "") (VNum (nVar v'))
       | Just _ <- mine e' -> defineTgt' "flex-flex In In0"(NamedPort p' "") (VNum (nVar v))
       | otherwise -> mkYield "flexFlex" (S.fromList [e, e']) >> unifyNum mine (nVar v) (nVar v')

  lhsStrictMono :: StrictMono (VVar Z) -> NumVal (VVar Z) -> Checking ()
  lhsStrictMono (StrictMono 0 mono) num = lhsMono mono num
  lhsStrictMono (StrictMono n mono) num = do
    num <- traceChecking "lhsSM demandEven" demandEven num
    unifyNum mine (NumValue 0 (StrictMonoFun (StrictMono (n - 1) mono))) num

  lhsMono :: Monotone (VVar Z) -> NumVal (VVar Z) -> Checking ()
  lhsMono (Linear (VPar e)) num | x <- mine e, trail ("lhsMono\n  " ++ show e ++ "\n  " ++ show num ++ "\n  " ++ show x) False = undefined
  -- x = f(x) has 3 solutions, otherwise we should complain!
  lhsMono lhs@(Linear (VPar e)) num | [e'] <- numVars num, e == e' = case num of
    (NumValue 0 (StrictMonoFun sm)) -> case anyDoubsAnyFulls sm of
      (True, _) -> lhsMono lhs (nConstant 0)
      (False, True) -> mkYield "lhsMono2Sols" (S.singleton e) >>
                       unifyNum mine (nVar (VPar e)) num
      (False, False) -> pure ()
    _ -> err . UnificationError $ "Can't make " ++ show e ++ " = " ++ show num
  lhsMono (Linear (VPar e)) num = case mine e of
    Just loc -> loc -! solveNumMeta mine e num
    _ -> mkYield "lhsMono" (S.singleton e) >>
         unifyNum mine (nVar (VPar e)) num
  lhsMono (Full sm) (NumValue 0 (StrictMonoFun (StrictMono 0 (Full sm'))))
    = lhsFun00 (StrictMonoFun sm) (NumValue 0 (StrictMonoFun sm'))
  lhsMono m@(Full _) (NumValue 0 gro) = trail "lhsMono swaps" $ lhsFun00 gro (NumValue 0 (StrictMonoFun (StrictMono 0 m)))
  lhsMono (Full sm) (NumValue up gro) = do
    smPred <- traceChecking "lhsMono demandSucc" demandSucc (NumValue 0 (StrictMonoFun sm))
    _ <- numEval S0 sm
    -- trailM $ "succ now " ++ show (quoteNum Zy sm)
    unifyNum mine (n2PowTimes 1 (nFull smPred)) (NumValue (up - 1) gro)

  anyDoubsAnyFulls :: StrictMono (VVar Z) -> (Bool, Bool)
  anyDoubsAnyFulls (StrictMono k (Full rest)) = let (ds,_) = anyDoubsAnyFulls rest in (k > 0 || ds, True)
  anyDoubsAnyFulls (StrictMono k (Linear _)) = (k > 0, False)

  demand0 :: NumVal (VVar Z) -> Checking ()
  demand0 (NumValue 0 Constant0) = pure ()
  demand0 n@(NumValue 0 (StrictMonoFun (StrictMono _ mono))) = case mono of
    Linear (VPar e) | Just _ <- mine e -> solveNumMeta mine e (nConstant 0)
    Full sm -> demand0 (NumValue 0 (StrictMonoFun sm))
    _ -> err . UnificationError $ "Couldn't force " ++ show n ++ " to be 0"
  demand0 n = err . UnificationError $ "Couldn't force " ++ show n ++ " to be 0"

  -- Complain if a number isn't a successor, else return its predecessor
  demandSucc :: NumVal (VVar Z) -> Checking (NumVal (VVar Z))
      --   2^k * x
      -- = 2^k * (y + 1)
      -- = 2^k + 2^k * y
      -- Hence, the predecessor is (2^k - 1) + (2^k * y)
  demandSucc (NumValue k x) | k > 0 = pure (NumValue (k - 1) x)
  demandSucc (NumValue 0 (StrictMonoFun (mono@(StrictMono k (Linear (VPar e))))))
    | Just loc <- mine e = do
      pred <- loc -! traceChecking "makePred" makePred e
      pure (nPlus ((2^k) - 1) (nVar (VPar pred)))

  --   2^k * full(n + 1)
  -- = 2^k * (1 + 2 * full(n))
  -- = 2^k + 2^(k + 1) * full(n)

    | otherwise = do
      mkYield "demandSucc" (S.singleton e)
      nv <- quoteNum Zy <$> numEval S0 mono
      demandSucc nv

  -- if it's not "mine" should we wait?
  demandSucc (NumValue 0 (StrictMonoFun (StrictMono k (Full nPlus1)))) = do
    n <- traceChecking "demandSucc" demandSucc (NumValue 0 (StrictMonoFun nPlus1))
    -- foo <- numEval S0 x
    -- trailM $ "ds: " ++ show x ++ " -> " ++ show (quoteNum Zy foo)
    pure $ nPlus ((2 ^ k) - 1) $ n2PowTimes (k + 1) $ nFull n
  demandSucc n = err . UnificationError $ "Couldn't force " ++ show n ++ " to be a successor"

  -- Complain if a number isn't even, otherwise return half
  demandEven :: NumVal (VVar Z) -> Checking (NumVal (VVar Z))
  demandEven (NumValue up gro) = case up `divMod` 2 of
    (up, 0) -> nPlus up <$> traceChecking "evenGro" evenGro gro
    (up, 1) -> nPlus (up + 1) <$> traceChecking "oddGro" oddGro (NumValue 0 gro)
   where
    evenGro :: Fun00 (VVar Z) -> Checking (NumVal (VVar Z))
    evenGro Constant0 = pure $ nConstant 0
    evenGro (StrictMonoFun (StrictMono 0 mono)) = case mono of
      Linear (VPar e)
        | Just loc <- mine e -> loc -! do
          -- trailM $ "Calling makeHalf (" ++ show e ++ ")"
          half <- traceChecking "makeHalf" makeHalf e
          pure (NumValue 0 (StrictMonoFun (StrictMono 0 (Linear (VPar half)))))
        | otherwise -> do
          mkYield "evenGro" (S.singleton e)
          nv <- quoteNum Zy <$> numEval S0 mono
          demandEven nv
      Full sm -> nConstant 0 <$ demand0 (NumValue 0 (StrictMonoFun sm))
    evenGro (StrictMonoFun (StrictMono n mono)) = pure (NumValue 0 (StrictMonoFun (StrictMono (n - 1) mono)))

    -- Check a numval is odd, and return its rounded down half
    oddGro :: NumVal (VVar Z) -> Checking (NumVal (VVar Z))
    oddGro x = do
     pred <- demandSucc x
     demandEven pred
