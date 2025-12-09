module Brat.Machine where

import Brat.Naming (Name, Namespace)
import Brat.Graph (Graph, NodeType (..), Node (BratNode, KernelNode), wiresTo, MatchSequence (..), PrimTest (..), TestMatchData (..))
import Brat.Syntax.Port (OutPort(..))
import Brat.Syntax.Common
import Brat.Syntax.Value

import Hasochism

import qualified Data.Map as M
import Bwd

data Frame where
    BratValues :: EvalEnv -> Frame
    -- Node weight, name+offset requested, state of evaluating inputs:
    -- (values computed, ports whose values still needed)
    EvalNodeInputs :: Node -> OutPort -> Bwd Value -> [OutPort] -> Frame
    HandleNodeOutputs :: OutPort -> Frame
  deriving Show

data Task where
    EvalPort :: OutPort -> Task
    Suspend :: [Frame] -> Task -> Task
    EvalNode :: Node -> [Value] -> Task
    Use :: Value -> Task -- searches for EvalNodeInputs
    NodeFinished :: [Value] -> Task -- searches for HandleNodeOutputs
  deriving Show

lookupOutport :: Bwd Frame -> OutPort -> Maybe Value
lookupOutport B0 _ = Nothing
lookupOutport (fz :< BratValues env) p | Just v <- M.lookup env p = Just v
lookupOutport (fz :< _) p = lookupOutport fz p

nextInput :: Graph -> Bwd Frame -> Node -> OutPort -> Bwd Value -> [OutPort] -> Task
-- EvalNodeInputs is "missing" one input (between valz and ports), i.e. the one that's the current Task
-- (whereas nextInput has them all)
nextInput g fz nw requested valz (p:ps) = run g (fz :< EvalNodeInputs nw requested valz ps) (EvalPort p)
nextInput g fz nw requested valz [] = run g (fz :< HandleNodeOutputs requested) (EvalNode nw (valz <>> []))

updateCache (fz :< BratValues env) port_vals = fz :< (BratValues $ foldr (uncurry M.insert) env port_vals)
updateCache (fz :< f) pvs = (updateCache fz pvs) :< f
-- updateCache B0 pvs = B0 :< (M.fromList pvs)

run :: Graph -> Bwd Frame -> Task -> Task
run g@(nodes, wires) fz (EvalPort p@(Ex name offset)) = case lookupOutport fz p of
    Just v -> run g fz (Use v)
    Nothing -> 
        -- might be good to check M.keys == [0,1,....] here
        let srcs = M.elems (M.fromList [(tgtPort, src) | (src, _, In _ tgtPort) <- wiresTo name g])
        in nextInput g fz (nodes M.! name) p B0 srcs
run g (fz :< EvalNodeInputs nw req valz rem) (Use v) = nextInput g fz nw req (valz :< v) rem
-- run g (fz :< f) (Use v) = let t = run g fz (Use v) in  -- not yet
run g (fz :< HandleNodeOutputs req@(Ex name offset)) (NodeFinished vals) =
    run g (updateCache fz [(Ex name i, val) | (i, val) <- zip [0..] vals]) (Use (vals !! offset))
run g fz (EvalNode nw inputVals) = todo -- case nw of

run g (fz :< f) (Suspend fs t) = run g fz (Suspend (f:fs) t)
run _ B0 t@(Suspend _ _) = t
run g fz t = run g fz (Suspend [] t)

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

