module Brat.Machine (runInterpreter) where

import Brat.Checker.Monad (CaptureSets)
import Brat.Checker.Types (Store, initStore)
import Brat.Compiler (compileToGraph)
--import Brat.Compile.Hugr (compileKernel, makeIO, makeCS, addEdge, addNode, CompilationState(hugr), Container(..))
import Brat.Compile.Hugr
import Brat.Constructors.Patterns
import Brat.Naming (Name, Namespace, split)
import qualified Brat.Naming as Naming
import Brat.Graph (Graph, NodeType (..), Node (BratNode, KernelNode), wiresTo, MatchSequence (..), PrimTest (..), TestMatchData (..), emptyGraph)
import Brat.QualName (QualName, plain)
import Brat.Syntax.Simple (SimpleTerm(..))
import Brat.Syntax.Port (OutPort(..))
import Brat.Syntax.Common
import Brat.Syntax.Value

import Data.Hugr
import qualified Data.HugrGraph as HG
import Hasochism

import Control.Monad.State (execState, gets, evalState)
import qualified Data.ByteString.Lazy as BS
import Data.Maybe (fromMaybe, fromJust)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as M
import qualified Data.Set as S
import Bwd
import Util (zipSameLength)

import Debug.Trace

type GraphInfo = (Graph, Store, Namespace, CaptureSets)

runInterpreter :: [FilePath] -> String -> String -> IO ()
runInterpreter libDirs file runFunc = do
    (root, (venv, _, _, st, outerGraph, capSets)) <- compileToGraph libDirs file
    --print (show outerGraph)
    let outPorts = [op | (NamedPort op _, _ty) <- venv M.! (plain runFunc)]
    let outTask = evalPorts (outerGraph, st, root, capSets) (B0 :< BratValues M.empty) B0 outPorts
    -- we hope outTask is a Finished. Or a Suspend.
    case outTask of
      Finished [(KernelV hugr)] -> do
        --putStrLn "Final Hugr Graph:"
        BS.putStr (HG.to_json hugr)
      _ -> print outTask

data Frame where
    BratValues :: EvalEnv -> Frame
    -- Optionally "what to do when all ports evaled" - Node weight, name+offset requested
    -- then state of evaluating inputs: (values computed, ports whose values still needed)
    EvalPorts :: Bwd Value -> [OutPort] -> Frame
    -- We're waiting for a task to deliver us all of the inputs for this node,
    -- then we can deliver the outputs.
    AwaitNodeInputs :: OutPort -> Frame
    -- Also responsible for caching all node outputs
    SelectFromNodeOutputs :: OutPort -> Frame
    -- have arguments to function, waiting for the function:
    CallWith :: [Value] -> Frame
    ReturnTo :: Bwd Frame -> Frame
    Alternatives :: [(TestMatchData Brat, Name)] -> [Value] -> Frame
    PerformMatchTests :: [(Src, PrimTest (BinderType Brat))] -> [(Src, BinderType Brat)] -> Name -> Frame
    DoSplices :: HG.HugrGraph HG.NodeId -> HG.NodeId -> [(HG.NodeId, OutPort)] -> Frame

divider = replicate 78 '-'

instance Show Frame where
  show f = unlines $
   [""
   ,divider
   ] ++ showFrame f

showFrame :: Frame -> [String]
showFrame (BratValues env) = ["BratValues", show env]
showFrame (EvalPorts vz ports) = ["EvalPorts", show vz, "<-- You are here -->", show ports]
showFrame (AwaitNodeInputs out) = ["AwaitNodeInputs", show out ++ "<-- You are here"]
showFrame (SelectFromNodeOutputs out) = ["SelectFromNodeOutputs", show out]
showFrame (CallWith vz) = ["CallWith", show vz]
showFrame (ReturnTo fz) = "ReturnTo" : (("> " ++) <$> showFrames fz)
showFrame (Alternatives matches vz) = ["Alternatives", show matches, show vz]
showFrame (PerformMatchTests tests srcs node) = ["PerformMatchTests", show tests, show srcs, show node] -- TODO
showFrame (DoSplices hg src hugrs) = ["DoSplices", show hg, show src, show hugrs]

showFrames :: Bwd Frame -> [String]
showFrames = foldMap (\f -> divider : showFrame f)

data Task where
    EvalPort :: OutPort -> Task
    Suspend :: [Frame] -> Task -> Task
    EvalNode :: Name -> [Value] -> Task
    Use :: Value -> Task -- searches for EvalPorts or DoSplices
    Finished :: [Value] -> Task -- searches for SelectFromNodeOutputs, or final result
    TryNextMatch :: Task
    NoMatch :: Task
    StuckOnNode :: Name -> Node -> Task
  deriving Show

lookupOutport :: Bwd Frame -> OutPort -> Maybe Value
lookupOutport B0 _ = Nothing
-- TODO: Highly suspect that we keep looking beyond the most local cache
lookupOutport (_ :< BratValues env) p | Just v <- M.lookup p env = Just v
lookupOutport (fz :< _) p = lookupOutport fz p

evalPorts :: GraphInfo -> Bwd Frame -> Bwd Value -> [OutPort] -> Task
-- EvalPorts is "missing" one input (between valz and ports), i.e. the one that's the current Task
-- (whereas evalPorts has them all)
evalPorts g fz valz (p:ps) = run g (fz :< EvalPorts valz ps) (EvalPort p)
evalPorts g fz valz [] = run g fz (Finished (valz <>> []))

getNodeInputs :: GraphInfo -> Name -> [OutPort]
getNodeInputs (g, _, _, _) name = M.elems (M.fromList [(tgtPort, src) | (src, _, In _ tgtPort) <- wiresTo name g])

evalNodeInputs :: GraphInfo -> Bwd Frame -> Name -> Task
evalNodeInputs gi fz name =
    -- might be good to check M.keys == [0,1,....] here
    evalPorts gi fz B0 (getNodeInputs gi name)

updateCache (fz :< BratValues env) port_vals = fz :< (BratValues $ foldr (uncurry M.insert) env port_vals)
updateCache (fz :< f) pvs = (updateCache fz pvs) :< f
-- updateCache B0 pvs = B0 :< (M.fromList pvs)

evalSplices :: GraphInfo -> Bwd Frame -> HG.HugrGraph HG.NodeId -> [(HG.NodeId, OutPort)] -> Task
evalSplices gi fz hugr [] = run gi fz (Finished [KernelV hugr])
evalSplices gi fz hugr ((nid, outport):rest) =
    run gi (fz :< DoSplices hugr nid rest) (EvalPort outport)

run :: GraphInfo -> Bwd Frame -> Task -> Task
--run g fz t | trace ("RUN: " ++ show fz ++ "\n" ++ show t) False = undefined

-- Tasks that push new frames onto the stack to do things
run gi@(g@(nodes, wires), _, _, _) fz (EvalPort p@(Ex name offset)) = case lookupOutport fz p of
    Just v -> run gi fz (Use v)
    Nothing -> evalNodeInputs gi (fz :< AwaitNodeInputs p) name
run gi@(g@(nodes, _), st, root, cs) fz t@(EvalNode n ins) = case nodes M.! n of
    --nw | trace ("EVALNODE " ++ show nw) False -> undefined
    (BratNode (Const st) _ _) -> run gi fz (Finished [evalSimpleTerm st])
    (BratNode (ArithNode op) _ _) -> run gi fz (Finished [evalArith op ins])
    (BratNode Id _ _) -> run gi fz (Finished ins)
    (BratNode (Eval func) _ _) -> run gi (fz :< CallWith ins) (EvalPort func)
    (BratNode (Box src tgt) [] [(_, VFun Kerny _)]) ->
        let (sub, newRoot) = split "box" root
            (hugr, splices) = compileKernel (sub, st, g) "box" n
        in evalSplices (g, st, newRoot, cs) fz hugr splices
    (BratNode (Box src tgt) _ _) ->
        let captureSet = fromMaybe M.empty (M.lookup n cs)
            capturedSrcs = S.fromList [src | (NamedPort src _name, _ty) <- concat (M.elems captureSet)]
        in run gi fz (Finished [ThunkV $ BratClosure (captureEnv fz capturedSrcs) src tgt])
    (BratNode (PatternMatch (c:|cs)) _ _) -> run gi (fz :< Alternatives (c:cs) ins) TryNextMatch
    (BratNode (Constructor c) _ _) -> run gi fz (Finished [evalConstructor c ins])
    (BratNode (Dummy k) _ _) -> run gi fz (Finished [DummyV])
    (BratNode (Prim (ext, op)) [] [(_, VFun Braty cty)]) -> run gi fz (Finished [ThunkV (BratPrim ext op cty)])
    nw -> run gi fz (StuckOnNode n nw)

-- Tasks that unwind the stack looking for what to do with the result
----Suspend
run gi (fz :< f) (Suspend fs t) = run gi fz (Suspend (f:fs) t)
run _ B0 t@(Suspend _ _) = t
---- Use (single value)
run gi (fz :< EvalPorts valz rem) (Use v) = evalPorts gi fz (valz :< v) rem
run gi (fz :< DoSplices hugr nid rest) (Use v) =
    let (KernelV sub_hugr) = v
        hugr' = execState (HG.splice_prepend nid sub_hugr) hugr
    in evalSplices gi fz hugr' rest
run gi (fz :< CallWith inputs) (Use (ThunkV (BratClosure env src tgt))) =
    let env_with_args = foldr (uncurry M.insert) env [(Ex src off, val) | (off, val) <- zip [0..] inputs]
    in evalNodeInputs gi (B0 :< ReturnTo fz :< (BratValues env_with_args)) tgt
run gi@(g,st,ns,cs) (fz :< CallWith inputs) (Use (ThunkV (BratPrim ext op cty)))
 | (hugrNS,newRoot) <- split "hugr" ns, Just outs <- runPrim hugrNS (ext,op) inputs = run (g,st,newRoot,cs) fz (Finished outs)

---- Finished (list of values)
run gi (fz :< AwaitNodeInputs req@(Ex name offset)) (Finished inputs) =
    run gi (fz :< SelectFromNodeOutputs req) (EvalNode name inputs)
run gi (fz :< SelectFromNodeOutputs req@(Ex name offset)) (Finished outputs) =
    run gi (updateCache fz [(Ex name i, val) | (i, val) <- zip [0..] outputs]) (Use (outputs !! offset))
run gi (B0 :< ReturnTo fz) (Finished vals) = run gi fz (Finished vals)

-- TryNextMatch
run gi (fz :< Alternatives [] _) TryNextMatch = run gi fz NoMatch
run gi (fz :< Alternatives ((TestMatchData _ ms, box):cs) ins) TryNextMatch =
    let MatchSequence matchInputs matchTests matchOutputs = ms
        testInputs = M.fromList (fromJust $ zipSameLength [src | (NamedPort src _,_ty) <- matchInputs] ins)
        outEnv = doAllTests testInputs matchTests
    in case {- trace ("outEnv: " ++ show outEnv ++ "\nmatchOutputs: " ++ show matchOutputs) -} outEnv of
        Nothing -> run gi (fz :< Alternatives cs ins) TryNextMatch
        Just env ->
            let vals = [miniEval gi env src | (NamedPort src _, _) <- matchOutputs]
            in run gi (fz :< CallWith vals) (EvalPort $ Ex box 0)

run gi (fz :< BratValues _) t = run gi fz t
run gi B0 t = t
run gi fz t = run gi fz (Suspend [] t)

runPrim :: Namespace -> (String, String) -> [Value] -> Maybe [Value]
runPrim _ ("arith","i2f") [IntV v] = Just [FloatV (fromIntegral v)]
runPrim ns ("tket", op) [FloatV th] | op `elem` ["CRx", "CRy", "CRz"] = Just [KernelV (makeParametrisedGateHugr ns op th 2)]
runPrim _ _ _ = Nothing

makeParametrisedGateHugr :: Namespace -> {- Op name: -} String -> {- angle arg: -} Double -> Int -> HG.HugrGraph HG.NodeId
makeParametrisedGateHugr ns op th nqubits =
  let (ns', newRoot) = split "" ns in
   hugr $ flip execState (makeCS (emptyGraph, newRoot, initStore) (dfgHugr ns')) $ do
     parent <- gets (HG.root . hugr)
     Ctr {parent,input,output} <- makeIO "" parent
     onHugr $ HG.setOp input (OpIn (InputNode [HTQubit, HTQubit] []))
     onHugr $ HG.setOp output (OpOut (OutputNode [HTQubit, HTQubit] []))
     -- TODO: Make this a rotation (using hvRotation) when we use the actual TKET
     -- ops, we're just targeting dummy ops in the BRAT extension for the sake of
     -- getting things going until hugr is updated.
     constTh <- addNode "k_th" (parent, OpConst (ConstOp (hvFloat th)))
     th <- addNode "th" (parent, OpLoadConstant (LoadConstantOp hugrFloat))
     gate <- addNode "gate" (parent, addMetadata [("Our","Gate")] $ OpCustom gateOp)
     addEdge (Port input 0, Port gate 0)
     addEdge (Port input 1, Port gate 1)
     addEdge (Port constTh 0, Port th 0)
     addEdge (Port th 0, Port gate 2)
     addEdge (Port gate 0, Port output 0)
     addEdge (Port gate 1, Port output 1)
 where
  dfgHugr :: Namespace -> HG.HugrGraph HG.NodeId
  dfgHugr = evalState (HG.new "" (OpDFG (DFG signature [])))

  signature = FunctionType
   { input = [HTQubit | _ <- [1..nqubits]]
   , output = [HTQubit | _ <- [1..nqubits]]
   , extensions = bratExts
   }

  gateOp = CustomOp
   { extension = "BRAT" -- TODO: Make this "tket.quantum"
   , op_name = op
   , signature_ = FunctionType
                  { input = [HTQubit | _ <- [1..nqubits]]
                             ++ [hugrFloat] -- TODO: Make this hugrRotation
                  , output = [HTQubit | _ <- [1..nqubits]]
                  , extensions = bratExts
                  }
   , args = []
   }



miniEval :: GraphInfo -> EvalEnv -> OutPort -> Value
miniEval _ env x | Just v <- M.lookup x env = v
miniEval gi@((nodes, _), _, _, _) env (Ex node 0) =
  let inputs = miniEval gi env <$> getNodeInputs gi node
  in  case nodes M.! node of
        BratNode (ArithNode op) _ _ -> evalArith op inputs
        BratNode (Const x) _ _ -> evalSimpleTerm x
        BratNode (Constructor c) _ _ -> evalConstructor c inputs
        BratNode Id _ _ | [v] <- inputs -> v
        nw -> error $ "miniEval: " ++ show nw

evalConstructor :: QualName -> [Value] -> Value
evalConstructor CTrue [] = BoolV True
evalConstructor CFalse [] = BoolV False
evalConstructor CZero [] = IntV 0
evalConstructor CSucc [IntV n] = IntV (n + 1)
evalConstructor CDoub [IntV n] = IntV (2 * n)
evalConstructor CNil [] = VecV []
evalConstructor CCons [hd, VecV tl] = VecV (hd:tl)
evalConstructor CSnoc [VecV tl, hd] = VecV (tl ++ [hd])
evalConstructor CConcatEqEven [VecV ls, VecV rs] = VecV (ls ++ rs)
evalConstructor CRiffle [VecV evens, VecV odds] = VecV (riffle evens odds)
 where
  riffle [] [] = []
  riffle (e:es) (o:os) = e:o:riffle es os
evalConstructor CQubit [] = DummyV
evalConstructor CConcatEqOdd [VecV ls, mid, VecV rs] = VecV (ls ++ mid:rs)
evalConstructor name _ = error $ "Internal error: Unhandled constructor " ++ show name

doAllTests :: EvalEnv -> [(Src, PrimTest (BinderType Brat))] -> Maybe EvalEnv
doAllTests env [] = Just env
doAllTests env ((NamedPort outport _, test):tests) =
  case test of
    PrimLitTest term -> if testLiteral term (env M.! outport)
                        then doAllTests env tests
                        else Nothing
    PrimCtorTest ctor ty _ outSrcs -> do
      outputs <- testCtor ty ctor (env M.! outport)
      doAllTests (env `M.union` M.fromList (zip (end . fst <$> outSrcs) outputs)) tests

captureEnv :: Bwd Frame -> S.Set OutPort -> EvalEnv
captureEnv B0 _ = M.empty
captureEnv (fz :< BratValues env) keys = M.union (captureEnv fz keys) (M.filterWithKey (\k _ -> S.member k keys) env)
captureEnv (fz :< _) keys = captureEnv fz keys

evalSimpleTerm :: SimpleTerm -> Value
evalSimpleTerm (Num x) = IntV x
evalSimpleTerm (Float x) = FloatV x
evalSimpleTerm t = error ("todo " ++ show t)

evalArith :: ArithOp -> [Value] -> Value
evalArith op [IntV x, IntV y] = IntV $ case op of
  Add -> x + y
  Sub -> x - y
  Mul -> x * y
  Div -> div x y
  Pow -> x ^ y
evalArith op [FloatV x, FloatV y] = FloatV $ case op of
  Add -> x + y
  Sub -> x - y
  Mul -> x * y
  Div -> x / y
  Pow -> x ** y
evalArith _ _ = error "Bad arith inputs"

testLiteral :: SimpleTerm -> Value -> Bool
testLiteral (Num x) (IntV y) = x == y
testLiteral (Float x) (FloatV y) = x == y
testLiteral _ _ = error "Internal error: Unexpected literal test"

testCtor :: QualName -> QualName -> Value -> Maybe [Value]
testCtor CBool CTrue (BoolV True) = Just []
testCtor CBool CFalse (BoolV False) = Just []
testCtor CNat CZero (IntV 0) = Just []
testCtor CNat CSucc (IntV x) | x > 0 = Just [IntV (x - 1)]
testCtor CVec CNil (VecV []) = Just []
testCtor CVec CCons (VecV (v:vs)) = Just [v, VecV vs]
testCtor CVec CConcatEqEven (VecV vs) = do
  (half, 0) <- pure (length vs `divMod` 2)
  (xs, ys) <- pure (splitAt half vs)
  pure [VecV xs, VecV ys]
testCtor CVec CRiffle (VecV vs) = do
  (evens, odds) <- evenOdds vs
  pure [VecV evens, VecV odds]
 where
  evenOdds :: [a] -> Maybe ([a], [a])
  evenOdds [] = pure ([], [])
  evenOdds [x] = Nothing
  evenOdds (x:y:xs) = do
    (evens, odds) <- evenOdds xs
    pure (x:evens, y:odds)

testCtor CVec CConcatEqOdd (VecV vs) = do
  (half, 1) <- pure (length vs `divMod` 2)
  (xs, y:zs) <- pure (splitAt half vs)
  pure [VecV xs, y, VecV zs]
testCtor _ _ _ = Nothing

data Value =
    IntV Int
  | FloatV Double
  | BoolV Bool
  | VecV [Value]
  | ThunkV BratThunk
  | KernelV (HG.HugrGraph HG.NodeId)
  | DummyV

data BratThunk =
    -- this might want to be [EvalEnv] or something like that
    BratClosure EvalEnv Name Name  -- Captured environment, src node, tgt node
  | BratPrim String String (CTy Brat Z)

instance Show Value where
  show (IntV x) = show x
  show (FloatV x) = show x
  show (BoolV x) = show x
  show (VecV xs) = show xs
  show (ThunkV _) = "<thunk>"
  show (KernelV k) = "Kernel (" ++ show k ++ ")"
  show DummyV = "Dummy"

type EvalEnv = M.Map OutPort Value
