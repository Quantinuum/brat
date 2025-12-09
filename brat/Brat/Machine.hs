module Brat.Machine (runInterpreter) where

import Brat.Compiler (compileToGraph)
import Brat.Naming (Name, Namespace)
import Brat.Graph (Graph, NodeType (..), Node (BratNode, KernelNode), wiresTo, MatchSequence (..), PrimTest (..), TestMatchData (..))
import Brat.QualName (plain)
import Brat.Syntax.Simple (SimpleTerm(..))
import Brat.Syntax.Port (OutPort(..))
import Brat.Syntax.Common
import Brat.Syntax.Value

import Hasochism

import qualified Data.Map as M
import Bwd

runInterpreter :: [FilePath] -> String -> String -> IO ()
runInterpreter libDirs file runFunc = do
    (_, (venv, _, _, _, outerGraph, _)) <- compileToGraph libDirs file
    print (show outerGraph)
    let outPorts = [op | (NamedPort op _, _ty) <- venv M.! (plain runFunc)]
    let outTask = evalPorts outerGraph (B0 :< BratValues M.empty) B0 outPorts
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
  deriving Show

data Task where
    EvalPort :: OutPort -> Task
    Suspend :: [Frame] -> Task -> Task
    EvalNode :: Node -> [Value] -> Task
    Use :: Value -> Task -- searches for EvalPorts
    Finished :: [Value] -> Task -- searches for HandleNodeOutputs, or final result
  deriving Show

lookupOutport :: Bwd Frame -> OutPort -> Maybe Value
lookupOutport B0 _ = Nothing
lookupOutport (_ :< BratValues env) p | Just v <- M.lookup p env = Just v
lookupOutport (fz :< _) p = lookupOutport fz p

evalPorts :: Graph -> Bwd Frame -> Bwd Value -> [OutPort] -> Task
-- EvalPorts is "missing" one input (between valz and ports), i.e. the one that's the current Task
-- (whereas evalPorts has them all)
evalPorts g fz valz (p:ps) = run g (fz :< EvalPorts valz ps) (EvalPort p)
evalPorts g fz valz [] = run g fz (Finished (valz <>> []))

updateCache (fz :< BratValues env) port_vals = fz :< (BratValues $ foldr (uncurry M.insert) env port_vals)
updateCache (fz :< f) pvs = (updateCache fz pvs) :< f
-- updateCache B0 pvs = B0 :< (M.fromList pvs)

run :: Graph -> Bwd Frame -> Task -> Task
-- Tasks that push new frames onto the stack to do things
run g@(nodes, wires) fz (EvalPort p@(Ex name offset)) = case lookupOutport fz p of
    Just v -> run g fz (Use v)
    Nothing -> 
        -- might be good to check M.keys == [0,1,....] here
        let srcs = M.elems (M.fromList [(tgtPort, src) | (src, _, In _ tgtPort) <- wiresTo name g])
        in evalPorts g (fz :< PortOfNode p) B0 srcs
run g fz (EvalNode (BratNode (Const st) _ _) []) = run g fz (Finished [evalSimpleTerm st])
run g fz (EvalNode (BratNode (ArithNode op) _ _) ins) = run g fz (Finished [evalArith op ins])
run g fz (EvalNode (BratNode Id _ _) ins) = run g fz (Finished ins)

-- Tasks that unwind the stack looking for what to do with the result
run g (fz :< f) (Suspend fs t) = run g fz (Suspend (f:fs) t)
run _ B0 t@(Suspend _ _) = t
run g (fz :< EvalPorts valz rem) (Use v) = evalPorts g fz (valz :< v) rem
run g@(nodes, _) (fz :< PortOfNode req@(Ex name offset)) (Finished inputs) =
    run g (fz :< HandleNodeOutputs req) (EvalNode (nodes M.! name) inputs)

run g (fz :< HandleNodeOutputs req@(Ex name offset)) (Finished outputs) =
    run g (updateCache fz [(Ex name i, val) | (i, val) <- zip [0..] outputs]) (Use (outputs !! offset))

run g (fz :< BratValues _) t = run g fz t
run g fz t = run g fz (Suspend [] t)


buildEnv :: Bwd Frame -> EvalEnv
buildEnv B0 = M.empty
buildEnv (fz :< BratValues env) = M.union (buildEnv fz) env
buildEnv (fz :< _) = buildEnv fz

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

