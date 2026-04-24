module Brat.Machine (runInterpreter) where

import Brat.Checker.Monad (CaptureSets)
import Brat.Checker.Types (Store, initStore)
import Brat.Compiler (compileToGraph)
import Brat.Compile.Hugr
import Brat.Constructors.Patterns
import Brat.Naming (Name, Namespace, split)
import Brat.Graph (Graph, NodeType (..), Node (BratNode), wiresTo, MatchSequence (..), PrimTest (..), TestMatchData (..), emptyGraph)
import Brat.QualName (QualName(..), plain)
import Brat.Syntax.Simple (SimpleTerm(..))
import Brat.Syntax.Common
import Brat.Syntax.Value

import Data.Hugr
import qualified Data.HugrGraph as HG
import Hasochism

import Control.Monad.State (execState, gets, evalState)
import qualified Data.Text.Lazy as T
import Data.Maybe (fromMaybe, fromJust, isNothing)
import Data.List (uncons)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as M
import qualified Data.Set as S
import Bwd
import Util (zipSameLength)

type GraphInfo = (Graph, Store, Namespace, CaptureSets)

runInterpreter :: [FilePath] -> String -> String -> IO (Either T.Text (HG.HugrGraph HG.NodeId))
runInterpreter libDirs file runFunc = do
    (root, (declEnv, _, st, outerGraph, capSets)) <- compileToGraph libDirs file
    let venv = M.map fst declEnv
    --print (show outerGraph)
    let outPorts = [op | (NamedPort op _, _ty) <- venv M.! (plain runFunc)]
    let outTask = evalPorts (outerGraph, st, root, capSets) (B0 :< BratValues M.empty) B0 outPorts
    -- we hope outTask is a Finished. Or a Suspend.
    pure $ case outTask of
      Finished [(KernelV hugr)] -> Right hugr
      _ -> Left $ T.pack $ show outTask

data Frame where
    BratValues :: EvalEnv -> Frame
    -- In process of evaluating a list of OutPorts: (values computed, ports still needed)
    -- (excluding the one that's in process of being evaluated)
    EvalPorts :: Bwd Value -> [OutPort] -> Frame
    -- We're waiting for a task to deliver us all of the inputs for this node,
    -- goal is to deliver the single requested OutPort (after evaluating the node)
    AwaitNodeInputs :: OutPort -> Frame
    -- Waiting for a task to deliver us all of the outputs for a node,
    -- goal is to deliver the single requested OutPort.
    SelectFromNodeOutputs :: OutPort -> Frame
    -- have arguments to function, waiting for the function:
    CallWith :: [Value] -> Frame
    ReturnTo :: Bwd Frame -> Frame
    Alternatives :: [(TestMatchData Brat, Name)] -> [Value] -> Frame
    PerformMatchTests :: [(Src, PrimTest (BinderType Brat))] -> [(Src, BinderType Brat)] -> Name -> Frame
    DoSplices :: HG.HugrGraph HG.NodeId -> HG.NodeId -> [(HG.NodeId, OutPort)] -> Frame
    -- Remaining thunks with their inputs, and rows output by prior thunks
    VectorisedFuncs :: [(BratThunk, [Value])] -> Bwd [Value] -> Frame

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
showFrame (VectorisedFuncs ths outs) = ["VectorisedFuncs", "remaining " ++ show (length ths) ++ " thunks", show outs]
showFrames :: Bwd Frame -> [String]
showFrames = foldMap (\f -> divider : showFrame f)

data Task where
    -- Evaluates a port (or retrieves value from cache)
    EvalPort :: OutPort -> Task
    Suspend :: [Frame] -> Task -> Task
    -- Evaluate a node given its inputs (graph edges, excluding e.g. func to Eval)
    EvalNode :: Name -> [Value] -> Task
    -- A single Outport value is ready; searches for EvalPorts or DoSplices to use it.
    Use :: Value -> Task
    -- Finished computing a list of values (all outputs of one node);
    -- searches for SelectFromNodeOutputs to use one, or is final result (of runInterpreter or ReturnTo).
    Finished :: [Value] -> Task
    -- Try the next clause in an Alternatives
    TryNextMatch :: Task
    -- No clause in an Alternatives matched
    NoMatch :: Task
    StuckOnNode :: Name -> Node -> Task
  deriving Show

lookupOutport :: Bwd Frame -> OutPort -> Maybe Value
lookupOutport B0 _ = Nothing
-- TODO: Might we need to look beyond the most local cache?
-- Believe "CaptureSets" are computed to ensure we don't need to.
lookupOutport (_ :< BratValues env) p = M.lookup p env
--lookupOutport (_ :< BratValues env) p | Just v <- M.lookup p env = Just v
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

runVectorisedThunks :: GraphInfo -> Bwd Frame -> [(BratThunk, [Value])] -> Bwd [Value] -> Task
runVectorisedThunks gi fz [] outs = run gi fz (Finished $ transposeRows2V $ outs <>> [])
 where
  -- outs accumulates a [Value] from each thunk, being a row.
  -- assemble corresponding elements from each row into a VecV,
  -- being that element of the output row of the vectorised thunk.
  transposeRows2V :: [[Value]] -> [Value]
  transposeRows2V rows = let rows' = map uncons rows
    in if all isNothing rows'
       then []
       else let (hds, tls) = unzip (map fromJust rows') in (VecV hds) : (transposeRows2V tls)
runVectorisedThunks gi fz ((th, inputs):ths) outs =
    runThunk gi (fz :< VectorisedFuncs ths outs) th inputs

run :: GraphInfo -> Bwd Frame -> Task -> Task
--run g fz t | trace ("RUN: " ++ show fz ++ "\n" ++ show t) False = undefined

runThunk :: GraphInfo -> Bwd Frame -> BratThunk -> [Value] -> Task
runThunk gi fz (BratClosure env src tgt) inputs =
    let env_with_args = foldr (uncurry M.insert) env [(Ex src off, val) | (off, val) <- zip [0..] inputs]
    in evalNodeInputs gi (fz :< (BratValues env_with_args)) tgt
runThunk (g,st,ns,cs) fz (BratPrim ext op _cty) inputs
 | (hugrNS,newRoot) <- split "hugr" ns, Just outs <- runPrim hugrNS (ext,op) inputs = run (g,st,newRoot,cs) fz (Finished outs)
runThunk gi fz (VectorisedThunks ths) inputs =
  runVectorisedThunks gi fz (fromJust $ zipSameLength ths $ transposeV2Rows inputs) B0
 where
  -- inputs to the vectorised thunk are a row of vectors;
  -- we run thunk#1 on the row formed from element#1 of each vector, and so on.
  transposeV2Rows :: [Value] -> [[Value]]
  transposeV2Rows vs
    | all isEmptyVecV vs = []
    | otherwise = let (hds, tls) = unzip $ map (\(VecV (hd:tl)) -> (hd, VecV tl)) vs in hds : (transposeV2Rows tls)
  isEmptyVecV :: Value -> Bool
  isEmptyVecV (VecV []) = True
  isEmptyVecV _ = False

-- Tasks that push new frames onto the stack to do things
run gi fz (EvalPort p@(Ex name _)) = case lookupOutport fz p of
    Just v -> run gi fz (Use v)
    Nothing -> evalNodeInputs gi (fz :< AwaitNodeInputs p) name
run gi@(g@(nodes, _), st, root, cs) fz (EvalNode n ins) = case nodes M.! n of
    --nw | trace ("EVALNODE " ++ show nw) False -> undefined
    (BratNode (Const st) _ _) -> run gi fz (Finished [evalSimpleTerm st])
    (BratNode (ArithNode op) _ _) -> run gi fz (Finished [evalArith op ins])
    (BratNode Id _ _) -> run gi fz (Finished ins)
    (BratNode (Eval func) _ _) -> run gi (fz :< CallWith ins) (EvalPort func)
    (BratNode (Box _ _) [] [(_, VFun Kerny _)]) ->
        let (sub, newRoot) = split "box" root
            (hugr, splices) = compileKernel (sub, st, g) "box" n
        in evalSplices (g, st, newRoot, cs) fz hugr splices
    (BratNode (Box src tgt) _ _) ->
        let captureSet = fromMaybe M.empty (M.lookup n cs)
            capturedSrcs = S.fromList [src | (NamedPort src _name, _ty) <- concat (M.elems captureSet)]
        in run gi fz (Finished [ThunkV $ BratClosure (captureEnv fz capturedSrcs) src tgt])
    (BratNode (PatternMatch (c:|cs)) _ _) -> run gi (fz :< Alternatives (c:cs) ins) TryNextMatch
    (BratNode (Constructor c) _ _) -> run gi fz (Finished [evalConstructor c ins])
    (BratNode (Dummy _) _ _) -> run gi fz (Finished [DummyV])
    (BratNode (Prim (ext, op)) [] [(_, VFun Braty cty)]) -> run gi fz (Finished [ThunkV (BratPrim ext op cty)])
    (BratNode (Selector stor) _ _) -> case (stor, ins) of
        (PrefixName [] "cons", [VecV (x:xs)]) -> run gi fz (Finished [x, VecV xs])
    (BratNode Replicate _ _) -> case ins of
      [IntV n, elem] -> run gi fz (Finished [(VecV (replicate n elem))])
    (BratNode MapFun _ _) -> case ins of
      -- We have a vector (or vec of vecs, n-dimensions) of functions
      [IntV len, VecV funs] -> run gi fz (Finished [dig len funs])
    nw -> run gi fz (StuckOnNode n nw)
 where
   -- Assuming a tree of VecV's whose leaf values are ThunkV's,
   -- Convert the bottom level of VecV's to VectorisedFuncs.
   -- We assume the tree is of uniform height (and arity at each *level*,
   -- perhaps varying between levels), this should be guaranteed by the checker.
   -- (TODO: consider encoding the expected levels/arities in the MapFun?)
  dig :: Int -> [Value] -> Value
  dig n vals
   | Just vecs <- mapM getVecs vals = VecV vecs
   | Just ths <- mapM getThunks vals
   , n == length vals = ThunkV (VectorisedThunks ths)
   where
    getVecs :: Value -> Maybe Value
    getVecs (VecV x) = Just (dig n x)
    getVecs _ = Nothing

    getThunks :: Value -> Maybe BratThunk
    getThunks (ThunkV th) = Just th
    getThunks _ = Nothing


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
run gi (fz :< CallWith inputs) (Use (ThunkV th)) = runThunk gi (B0 :< ReturnTo fz) th inputs

---- Finished (list of values)
run gi (fz :< AwaitNodeInputs req@(Ex name _)) (Finished inputs) =
    run gi (fz :< SelectFromNodeOutputs req) (EvalNode name inputs)
run gi (fz :< SelectFromNodeOutputs (Ex name offset)) (Finished outputs) =
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

-- Next element of VectorisedFuncs
run gi (fz :< VectorisedFuncs th_inps outs) (Finished vals) =
  runVectorisedThunks gi fz th_inps (outs :< vals)

run gi (fz :< BratValues _) t = run gi fz t
run _ B0 t = t
run gi fz t = run gi fz (Suspend [] t)

runPrim :: Namespace -> (String, String) -> [Value] -> Maybe [Value]
runPrim _ ("arith","i2f") [IntV v] = Just [FloatV (fromIntegral v)]
runPrim ns ("tket", op) [FloatV th] | op `elem` ["CRx", "CRy", "CRz"] = Just [KernelV (makeParametrisedGateHugr ns op th 2)]
runPrim _ _ _ = Nothing

makeParametrisedGateHugr :: Namespace -> {- Op name: -} String -> {- angle arg: -} Double -> Int -> HG.HugrGraph HG.NodeId
makeParametrisedGateHugr ns op th nqubits =
  let (ns', newRoot) = split "" ns in
   hugr $ flip execState (makeCS (emptyGraph, newRoot, initStore) (dfgHugr ns')) $ do
     parent <- gets (HG.getRoot . hugr)
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
evalConstructor CFull [IntV n] = IntV ((2 ^ n) - 1)
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
evalSimpleTerm (Text s) = StringV s
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
testCtor CVec CSnoc (VecV vs@(_:_)) = Just [VecV (init vs), last vs]
testCtor CList CNil (VecV []) = Just []
testCtor CList CCons (VecV (v:vs)) = Just [v, VecV vs]
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
  evenOdds [_] = Nothing
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
  | StringV String

data BratThunk =
    -- this might want to be [EvalEnv] or something like that
    BratClosure EvalEnv Name Name  -- Captured environment, src node, tgt node
  | BratPrim String String (CTy Brat Z)
  | VectorisedThunks [BratThunk] -- result of MapFun

instance Show Value where
  show (IntV x) = show x
  show (FloatV x) = show x
  show (BoolV x) = show x
  show (VecV xs) = show xs
  show (ThunkV (VectorisedThunks ths)) = "<vectorized thunk of " ++ show (length ths) ++ ">"
  show (ThunkV _) = "<thunk>"
  show (KernelV k) = "Kernel (" ++ show k ++ ")"
  show DummyV = "Dummy"
  show (StringV str) = show str

type EvalEnv = M.Map OutPort Value
