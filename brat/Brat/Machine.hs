module Brat.Machine (runInterpreter) where

import Brat.Checker.Monad (CaptureSets)
import Brat.Compiler (compileToGraph)
import Brat.Constructors.Patterns
import Brat.Naming (Name, Namespace)
import Brat.Graph (Graph, NodeType (..), Node (BratNode, KernelNode), wiresTo, MatchSequence (..), PrimTest (..), TestMatchData (..))
import Brat.QualName (QualName, plain)
import Brat.Syntax.Simple (SimpleTerm(..))
import Brat.Syntax.Port (OutPort(..))
import Brat.Syntax.Common
import Brat.Syntax.Value

import Hasochism

import Data.Maybe (fromMaybe, fromJust)
import Data.List.NonEmpty hiding ((!!), zip)
import qualified Data.Map as M
import qualified Data.Set as S
import Bwd
import Util (zipSameLength)

import Debug.Trace

type GraphInfo = (Graph, CaptureSets)

runInterpreter :: [FilePath] -> String -> String -> IO ()
runInterpreter libDirs file runFunc = do
    (_, (venv, _, _, _, outerGraph, capSets)) <- compileToGraph libDirs file
    print (show outerGraph)
    let outPorts = [op | (NamedPort op _, _ty) <- venv M.! (plain runFunc)]
    let outTask = evalPorts (outerGraph,capSets) (B0 :< BratValues M.empty) B0 outPorts
    -- we hope outTask is a Finished. Or a Suspend.
    print outTask
    pure ()

data Frame where
    BratValues :: EvalEnv -> Frame
    -- Optionally "what to do when all ports evaled" - Node weight, name+offset requested
    -- then state of evaluating inputs: (values computed, ports whose values still needed)
    EvalPorts :: Bwd Value -> [OutPort] -> Frame
    PortOfNode :: OutPort -> Frame
    HandleNodeOutputs :: OutPort -> Frame
    -- have arguments to function, waiting for the function:
    CallWith :: [Value] -> Frame
    ReturnTo :: Bwd Frame -> Frame
    Alternatives :: [(TestMatchData Brat, Name)] -> [Value] -> Frame
    PerformMatchTests :: [(Src, PrimTest (BinderType Brat))] -> [(Src, BinderType Brat)] -> Name -> Frame
  deriving Show

data Task where
    EvalPort :: OutPort -> Task
    Suspend :: [Frame] -> Task -> Task
    EvalNode :: Name -> [Value] -> Task
    Use :: Value -> Task -- searches for EvalPorts
    Finished :: [Value] -> Task -- searches for HandleNodeOutputs, or final result
    TryNextMatch :: Task
    NoMatch :: Task
    StuckOnNode :: Name -> Node -> Task
  deriving Show

lookupOutport :: Bwd Frame -> OutPort -> Maybe Value
lookupOutport B0 _ = Nothing
lookupOutport (_ :< BratValues env) p | Just v <- M.lookup p env = Just v
lookupOutport (fz :< _) p = lookupOutport fz p

evalPorts :: GraphInfo -> Bwd Frame -> Bwd Value -> [OutPort] -> Task
-- EvalPorts is "missing" one input (between valz and ports), i.e. the one that's the current Task
-- (whereas evalPorts has them all)
evalPorts g fz valz (p:ps) = run g (fz :< EvalPorts valz ps) (EvalPort p)
evalPorts g fz valz [] = run g fz (Finished (valz <>> []))

evalNodeInputs :: GraphInfo -> Bwd Frame -> Name -> Task
evalNodeInputs gi@(g,_) fz name =
    -- might be good to check M.keys == [0,1,....] here
    let srcs = M.elems (M.fromList [(tgtPort, src) | (src, _, In _ tgtPort) <- wiresTo name g])
    in evalPorts gi fz B0 srcs

updateCache (fz :< BratValues env) port_vals = fz :< (BratValues $ foldr (uncurry M.insert) env port_vals)
updateCache (fz :< f) pvs = (updateCache fz pvs) :< f
-- updateCache B0 pvs = B0 :< (M.fromList pvs)

run :: GraphInfo -> Bwd Frame -> Task -> Task
-- Tasks that push new frames onto the stack to do things
run gi@(g@(nodes, wires), _) fz (EvalPort p@(Ex name offset)) = case lookupOutport fz p of
    Just v -> run gi fz (Use v)
    Nothing -> evalNodeInputs gi (fz :< PortOfNode p) name
run g@((nodes, _), cs) fz t@(EvalNode n ins) = case nodes M.! n of
    (BratNode (Const st) _ _) -> run g fz (Finished [evalSimpleTerm st])
    (BratNode (ArithNode op) _ _) -> run g fz (Finished [evalArith op ins])
    (BratNode Id _ _) -> run g fz (Finished ins)
    (BratNode (Eval func) _ _) -> run g (fz :< CallWith ins) (EvalPort func)
    (BratNode (Box src tgt) _ _) ->
        let captureSet = fromMaybe M.empty (M.lookup n cs)
            capturedSrcs = S.fromList [src | (NamedPort src _name, _ty) <- concat (M.elems captureSet)]
        in run g fz (Finished [ThunkV $ BratClosure (captureEnv fz capturedSrcs) src tgt])
    (BratNode (PatternMatch (c:|cs)) _ _) -> run g (fz :< Alternatives (c:cs) ins) TryNextMatch
    nw -> run g fz (StuckOnNode n nw)


-- Tasks that unwind the stack looking for what to do with the result
----Suspend
run gi (fz :< f) (Suspend fs t) = run gi fz (Suspend (f:fs) t)
run _ B0 t@(Suspend _ _) = t
---- Use (single value)
run gi (fz :< EvalPorts valz rem) (Use v) = evalPorts gi fz (valz :< v) rem
run gi (fz :< CallWith inputs) (Use (ThunkV (BratClosure env src tgt))) =
    let env_with_args = foldr (uncurry M.insert) env [(Ex src off, val) | (off, val) <- zip [0..] inputs]
    in evalNodeInputs gi (B0 :< ReturnTo fz :< (BratValues env_with_args)) tgt

---- Finished (list of values)
run g (fz :< PortOfNode req@(Ex name offset)) (Finished inputs) =
    run g (fz :< HandleNodeOutputs req) (EvalNode name inputs)
run g (fz :< HandleNodeOutputs req@(Ex name offset)) (Finished outputs) =
    run g (updateCache fz [(Ex name i, val) | (i, val) <- zip [0..] outputs]) (Use (outputs !! offset))
run g (B0 :< ReturnTo fz) (Finished vals) = run g fz (Finished vals)

-- TryNextMatch
run g (fz :< Alternatives [] _) TryNextMatch = run g fz NoMatch
run g (fz :< Alternatives ((TestMatchData _ ms, box):cs) ins) TryNextMatch =
    let MatchSequence matchInputs matchTests matchOutputs = ms
        testInputs = M.fromList (fromJust $ zipSameLength [src | (NamedPort src _,_ty) <- matchInputs] ins)
        outEnv = doAllTests testInputs matchTests
    in case outEnv of
        Nothing -> run g (fz :< Alternatives cs ins) TryNextMatch
        Just env ->
            let vals = [env M.! src | (NamedPort src _, _) <- matchOutputs]
            in run g (fz :< CallWith vals) (EvalPort $ Ex box 0)

run g (fz :< BratValues _) t = run g fz t
run g B0 t = t
run g fz t = run g fz (Suspend [] t)

doAllTests :: EvalEnv -> [(Src, PrimTest (BinderType Brat))] -> Maybe EvalEnv
doAllTests env [] = Just env

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

data Value = 
    IntV Int 
  | FloatV Double 
  | BoolV Bool 
  | VecV [Value] 
  | ThunkV BratThunk
  | KernelV HugrKernel

data BratThunk =
    -- this might want to be [EvalEnv] or something like that
    BratClosure EvalEnv Name Name  -- Captured environment, src node, tgt node
  | BratPrim String String (CTy Brat Z)

data HugrKernel deriving Show

instance Show Value where
  show (IntV x) = show x
  show (FloatV x) = show x
  show (BoolV x) = show x
  show (VecV xs) = show xs
  show (ThunkV _) = "<thunk>"
  show (KernelV k) = "Kernel (" ++ show k ++ ")"

type EvalEnv = M.Map OutPort Value

