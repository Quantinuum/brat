module Brat.Compile.Interpreter (run, Value(..)) where

import Brat.Naming (Name, Namespace)
import Brat.Graph (Graph, NodeType (..), Node (BratNode, KernelNode), wiresTo, MatchSequence (..), PrimTest (..), TestMatchData (..))
import qualified Data.Map as M
import Brat.Syntax.Common
import Brat.Checker.Types (Store, VEnv)
import Brat.Syntax.Value
import Brat.Compile.Hugr
import Control.Monad.State
import Data.Tuple.HT (fst3)
import Control.Monad (forM, foldM, forM_)
import Brat.Syntax.Simple (SimpleTerm (..))
import Control.Arrow (first)
import Data.List.NonEmpty (NonEmpty(..), toList)
import Brat.QualName (QualName (PrefixName))
import Data.Hugr
import Debug.Trace (trace)
import Hasochism
import Brat.Constructors.Patterns


type HugrPort = TypedPort

data Value = 
    IntV Int 
  | FloatV Double 
  | BoolV Bool 
  | VecV [Value] 
  | ThunkV BratThunk
  | KernelV HugrKernel

data BratThunk =
    BratClosure (EvalEnv Brat) Name Name  -- Captured environment, src node, tgt node
  | BratPrim String String (CTy Brat Z)

data HugrKernel = 
    HugrFunc NodeId FunctionType       -- Either a user-defined function
  | HugrOp String String FunctionType [Value]  -- or an operation
 deriving Show

instance Show Value where
  show (IntV x) = show x
  show (FloatV x) = show x
  show (BoolV x) = show x
  show (VecV xs) = show xs
  show (ThunkV _) = "<thunk>"
  show (KernelV k) = "Kernel (" ++ show k ++ ")"

-- The data we're tracking for each port in the Brat graph
type family PortData (m :: Mode) where
  -- In Brat mode, we track a value for each port
  PortData Brat = Value
  -- In Kernel mode, we track a Hugr port for each Brat port
  -- in the Hugr that is currently under construction
  PortData Kernel = HugrPort


type EvalEnv m = M.Map OutPort (PortData m)

data EvalState = EvalState
 { evaledBratPorts :: EvalEnv Brat
 , evaledKernelPorts :: EvalEnv Kernel
 , moduleNode :: Maybe NodeId
 , currentParent :: Maybe NodeId
 }

type Eval a = StateT EvalState Compile a


emptyEvalEnv = EvalState 
 { evaledBratPorts = M.empty
 , evaledKernelPorts = M.empty
 , moduleNode = Nothing
 , currentParent = Nothing
}

getEvaled :: Modey m -> Eval (M.Map OutPort (PortData m))
getEvaled Braty = gets evaledBratPorts
getEvaled Kerny = gets evaledKernelPorts

putEvaled :: Modey m -> M.Map OutPort (PortData m) -> Eval ()
putEvaled Braty e = get >>= \st -> put (st { evaledBratPorts = e })
putEvaled Kerny e = get >>= \st -> put (st { evaledKernelPorts = e })

getModuleNode :: Eval NodeId
getModuleNode = get >>= \st -> case moduleNode st of
    Just node -> pure node
    Nothing -> do
      id <- lift $ freshNode "module"
      lift $ addOp (OpMod $ ModuleOp id) id
      put (st { moduleNode = Just id })
      pure id

evalPort :: Modey m -> OutPort -> Eval (PortData m)
evalPort my port@(Ex node offset) = getEvaled my >>= \evaled -> case M.lookup port evaled of
  Just v -> return v
  Nothing -> do
    graph@(nodes, _) <- lift $ gets bratGraph
    inputs <- forM (fst3 <$> wiresTo node graph) (evalPort my)  -- TODO: Very inefficient
    outputs <- case (my, nodes M.! node) of
      (Braty, BratNode thing _ _) -> evalNode Braty thing node inputs
      (Kerny, KernelNode thing _ _) -> evalNode Kerny thing node inputs
      _ -> error "Internal error: Brat vs kernel node mismatch"
    putEvaled my $ evaled `M.union` M.fromList [(Ex node i, v) | (i, v) <- zip [0..] outputs]
    pure $ outputs !! offset

evalNode :: Modey m -> NodeType m -> Name -> [PortData m] -> Eval [PortData m]
evalNode _ Source node _ = error $ "Internal error: Source should be in evaluated state: " ++ show node
evalNode _ Target _ inputs = pure inputs
evalNode _ Id _ inputs = pure inputs
evalNode Braty (Const term) _ [] = pure [evalSimpleTerm term]
evalNode Braty (Constructor con) _ inputs = pure [evalConstructor con inputs]
evalNode Braty (ArithNode op) _ inputs = pure [evalArith op inputs]
evalNode Braty (PatternMatch clauses) _ inputs = evalBratMatch (toList clauses) inputs
evalNode Braty (Eval thunk) _ inputs = evalPort Braty thunk >>= \case
  ThunkV th -> evalBratCall th inputs
  v -> error $ "Internal error: Not a thunk: " ++ show v
evalNode Kerny (Splice kernel) _ inputs = get >>= \st ->
  -- Spliced kernel is Brat value
  lift (evalStateT (evalPort Braty kernel) st) >>= \case
    KernelV k -> gets currentParent >>= \(Just parent) -> lift (evalKernelSplice k parent inputs)
    _ -> error "Internal error: Not a kernel value"
evalNode Braty (Box venv src tgt) node [] = do
  graph <- lift $ gets bratGraph
  case fst graph M.! node of
    (BratNode _ _ [(_, VFun Braty _)]) -> evalBratBox venv src tgt
    (BratNode _ _ [(_, VFun Kerny cty)]) -> evalKernelBox node src tgt cty
    _ -> error "Internal error: Unexpected box signature"
evalNode Braty (Prim (extension, op)) node [] = do
  graph <- lift $ gets bratGraph
  case fst graph M.! node of
    (BratNode _ _ [(_, VFun Braty cty)]) -> pure [ThunkV (BratPrim extension op cty)]
    (BratNode _ _ [(_, VFun Kerny cty)]) -> pure [KernelV (HugrOp extension op (body $ compileCTy cty) [])]
    _ -> error "Internal error: Unexpected prim signature"
evalNode _ thing _ _ = error $ "Internal error: Unexpected node in Brat box: " ++ show thing


evalBratBox :: VEnv -> Name -> Name -> Eval [Value]
evalBratBox venv src tgt = do
  -- Make a closure that captures the entire venv. Haskells laziness ensures
  -- that we won't run into problems with recursive definitions
  let envPorts = map (fst . first end) (concat $ M.elems venv)
  envVals <- forM envPorts (evalPort Braty)
  let env = M.fromList (zip envPorts envVals)
  pure [ThunkV (BratClosure env src tgt)]

evalBratCall :: BratThunk -> [Value] -> Eval [Value]
evalBratCall (BratClosure env src tgt) inputs = do
  st <- get
  graph <- lift $ gets bratGraph
  lift $ evalStateT (forM (wiresTo tgt graph) (\(port, _, _) -> evalPort Braty port))
          (st { evaledBratPorts = env `M.union` M.fromList (zip (Ex src <$> [0..]) inputs)
              , evaledKernelPorts = M.empty })
evalBratCall (BratPrim extension op (inRo :->> RPr (_, VFun Kerny cty) R0)) inputs = do
  let bratInTys = compileRo inRo
  let PolyFuncType _ (FunctionType inTys outTys _) = compileCTy cty
  pure [KernelV (HugrOp extension op (FunctionType (bratInTys ++ inTys) outTys []) inputs)]
evalBratCall _ _ = error "todo"

evalKernelBox :: Name -> Name -> Name -> CTy Kernel Z -> Eval [Value]
evalKernelBox node src tgt cty = do
  graph <- lift $ gets bratGraph
  -- Build a new Hugr function definition
  let name = "<kernel>"  -- TODO
  let polyFunTy@(PolyFuncType _ funTy@(FunctionType inTys outTys _)) = compileCTy cty
  moduleNode <- getModuleNode
  defNode <- lift $ addNode name (OpDefn $ FuncDefn moduleNode name polyFunTy)
  let kernelValue = KernelV (HugrFunc defNode funTy)
  -- Compile the kernel
  st <- get
  inpNode <- lift $ addNode "Input" (OpIn $ InputNode defNode inTys)
  outputs <- lift $ evalStateT (forM (wiresTo tgt graph) (\(port, _, _) -> evalPort Kerny port))
        -- Mark the kernel port as defined to enable recursive calls
      (st { evaledBratPorts = evaledBratPorts st `M.union` M.fromList [(Ex node 0, kernelValue)] 
          , evaledKernelPorts = M.fromList (zip (Ex src <$> [0..]) (zip (Port inpNode <$> [0..]) inTys)) 
          , currentParent = Just defNode })
  outNode <- lift $ addNode "Output" (OpOut $ OutputNode defNode outTys)
  lift $ forM_ (zip outputs [0..]) (\((p, _), i) -> addEdge (p, Port outNode i))
  pure [kernelValue]

evalKernelSplice :: HugrKernel -> NodeId -> [HugrPort] -> Compile [HugrPort]
evalKernelSplice (HugrFunc funcNode funcTy@(FunctionType _ outTys _)) parent inputs = do
  callNode <- addNode "Call" (OpCall (CallOp parent funcTy))
  forM_ inputs (\(p, _) -> addEdge (p, Port callNode 0))
  addEdge (Port funcNode 0, Port callNode (length inputs))
  pure (zip (Port callNode <$> [0..]) outTys)
evalKernelSplice (HugrOp extension op funcTy@(FunctionType _ outTys _) bratInputs) parent inputs = do
  bratInputs <- forM bratInputs (loadBratValue parent)
  node <- addNode (extension ++ "." ++ op) (OpCustom $ CustomOp parent extension op funcTy [])
  forM_ (zip (bratInputs ++ inputs) [0..]) (\((p, _), i) -> addEdge (p, Port node i))
  pure (zip (Port node <$> [0..]) outTys)

kernelToHugrFunc :: HugrKernel -> Eval HugrKernel
kernelToHugrFunc k@(HugrFunc _ _) = pure k
kernelToHugrFunc k@(HugrOp extension op funcTy@(FunctionType inTys outTys _) _) = do
  moduleNode <- getModuleNode
  let name = extension ++ "." ++ op
  defNode <- lift $ addNode name (OpDefn $ FuncDefn moduleNode name (PolyFuncType [] funcTy))
  inpNode <- lift $ addNode "Input" (OpIn $ InputNode defNode inTys)
  let inputs = zip (Port inpNode <$> [0..]) inTys
  outputs <- lift $ evalKernelSplice k defNode inputs
  outNode <- lift $ addNode "Output" (OpOut $ OutputNode defNode outTys)
  lift $ forM_ (zip outputs [0..]) (\((p, _), i) -> addEdge (p, Port outNode i))
  pure $ HugrFunc defNode funcTy

evalBratMatch :: [(TestMatchData Brat, Name)] -> [Value] -> Eval [Value]
evalBratMatch ((TestMatchData _ (MatchSequence matchInputs tests matchOutputs), rhs) : rest) inputs = do
  -- Add the inputs to the port map
  evaled <- getEvaled Braty
  putEvaled Braty $ evaled `M.union` M.fromList (zip (end . fst <$> matchInputs) inputs)
  -- Run the tests. TODO: Use something like andM instead
  result <- and <$> forM tests evalTest
  case result of
    True -> do
      outputs <- forM matchOutputs (evalPort Braty . end . fst)
      evalPort Braty (Ex rhs 0) >>= \case
          ThunkV th -> evalBratCall th outputs
          _ -> error "Internal error: Not a thunk"
    False -> evalBratMatch rest inputs
evalBratMatch [] _ = error "No matching clause"

evalTest :: (Src, PrimTest (BinderType Brat)) -> Eval Bool
evalTest (inputSrc, test) = do
  input <- evalPort Braty (end inputSrc)
  case test of
    PrimLitTest term -> pure $ testLiteral term input
    PrimCtorTest ctor ty _ outSrcs -> do
      case testCtor ty ctor input of
        Nothing -> pure False
        Just outputs -> do
          evaled <- getEvaled Braty
          putEvaled Braty $ evaled `M.union` M.fromList (zip (end . fst <$> outSrcs) outputs)
          pure True

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
testCtor _ _ _ = Nothing

evalConstructor :: QualName -> [Value] -> Value
evalConstructor CTrue [] = BoolV True
evalConstructor CFalse [] = BoolV False
evalConstructor CZero [] = IntV 0
evalConstructor CNil [] = VecV []
evalConstructor _ _ = error "Internal error: Unhandled constructor"

evalSimpleTerm :: SimpleTerm -> Value
evalSimpleTerm (Num x) = IntV x
evalSimpleTerm (Float x) = FloatV x
evalSimpleTerm _ = error "todo"

evalArith :: ArithOp -> [Value] -> Value
evalArith op [IntV x, IntV y] = IntV $ case op of
  Add -> x + y
  Sub -> y - x  -- What??
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

bratValueToHugr :: Value -> (HugrType, HugrValue)
bratValueToHugr (IntV x) = (hugrInt, hvInt x)
bratValueToHugr (FloatV x) = (hugrFloat, hvFloat x)
bratValueToHugr _ = error "todo"

loadBratValue :: NodeId -> Value -> Compile TypedPort
loadBratValue parent v = do
  let (ty, hugrValue) = bratValueToHugr v
  const <- addNode "Const" (OpConst $ ConstOp parent hugrValue)
  load <- addNode "LoadConst" (OpLoadConstant $ LoadConstantOp parent ty )
  addEdge (Port const 0, Port load 0)
  pure (Port load 0, ty)

-- buildKernelMatch :: [(TestMatchData Kernel, Name)] -> [Value] -> Eval [Value]
-- buildKernelMatch ((TestMatchData _ (MatchSequence matchInputs tests matchOutputs), rhs) : rest) inputs = do
--   _
 


evalMain :: Name -> [Value] -> Eval [Value]
evalMain main inputs = evalPort Braty (Ex main 0) >>= \case
  ThunkV th -> case inputs of
                            [] -> error "Missing arguments to entry point"
                            inputs -> evalBratCall th inputs >>= \case
                                          [KernelV k] -> pure . KernelV <$> kernelToHugrFunc k
                                          vs -> pure vs
  KernelV k -> case inputs of
                  [] -> pure . KernelV <$> kernelToHugrFunc k
                  _ -> error "Entry point is a kernel. Cannot supply arguments"
  v -> pure [v]

valuesOrHugr :: [Value] -> Compile (Either [Value] (Hugr Int))
valuesOrHugr [KernelV _] = do
  ns <- gets nodes
  es <- gets edges
  pure . Right $ renameAndSortHugr ns es
valuesOrHugr vs = pure (Left vs)

run :: Store -> Namespace -> Graph -> Name -> [Value] -> Either [Value] (Hugr Int)
run store ns graph main inputs =
  evalState (evalStateT (evalMain main inputs) emptyEvalEnv >>= valuesOrHugr) (emptyCS graph ns store)

