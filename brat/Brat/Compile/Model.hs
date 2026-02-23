-- Module for printing out a HugrGraph as a hugr model
module Brat.Compile.Model (toModelString) where

import Control.Monad.State
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.ByteString.Builder (Builder, word8)
import Data.Traversable (for)
import Data.List (delete)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, fromJust)

import Brat.Naming (Name, Namespace, fresh, root)
import Data.Hugr
import Data.HugrGraph
import qualified Brat.Naming as Name
import qualified Data.Hugr as H
import qualified Data.Hugr.Model as M

import qualified Data.ByteString as BS

import Debug.Trace

data ModelState = State
 { ns :: Namespace
 , nameCount :: Int
 -- Scoping fuckery
 , outVars :: Map.Map NodeId [(Int, M.LinkName)]
 , inpVars :: Map.Map NodeId [(Int, M.LinkName)]
 }

type Model = State ModelState -- out nodes that have been compiled

setOutVar :: NodeId -> [(Int, M.LinkName)] -> Model ()
setOutVar key val | trace ("setOutVar " ++ show key ++ " " ++ show val) False = undefined
setOutVar key val = do
  ms <- get
  let newVal = case Map.lookup key (outVars ms) of
        Just orig -> Map.union val orig
        Nothing -> Map.insert
  put (ms { outVars = Map.insert key newVal (outVars ms) })

setInpVar :: NodeId -> [(Int, M.LinkName)] -> Model ()
setInpVar key val | trace ("setInpVar " ++ show key ++ " " ++ show val) False = undefined
setInpVar key val = do
  ms <- get
  let newVal = case Map.lookup key (inpVars ms) of
        Just orig -> Map.union val orig
        Nothing -> Map.insert
  put (ms { inpVars = Map.insert key newVal (inpVars ms) })

-- The thing had better be defined!
-- TODO: Allow it not to be?
getInpVars :: NodeId -> Model (Int, M.LinkName)
getInpVars nid = gets (Map.! nid) inpVars

getOutVars :: NodeId -> Model (Int, M.LinkName)
getOutVars nid = gets (Map.! nid) outVars

freshName :: Model M.LinkName
freshName = do
  st <- get
  let (name, ns') = fresh (show (nameCount st)) (ns st)
  put (st { ns = ns', nameCount = nameCount st + 1 })
  pure name

freshInputLinks :: NodeId -> [a] -> Model [M.LinkName]
freshInputLinks nodeId xs = do
  links <- for xs (\_ -> (('%':) . show) <$> freshName)
  for (zip [0..] links) $ \(ix, link) -> setInpVar nodeId [(ix, link)]
  pure links

freshOutputLinks :: NodeId -> [a] -> Model [M.LinkName]
freshOutputLinks nodeId xs = do
  links <- for xs (\_ -> (('%':) . show) <$> freshName)
  for (zip [0..] links) $ \(ix, link) -> setOutVar nodeId [(ix, link)]
  pure links


convertMeta :: [(String, String)] -> [M.Term]
convertMeta [] = []
convertMeta ((key,val):xs) = M.Tuple [M.Item (M.Literal (M.LitStr key)), M.Item (M.Literal (M.LitStr key))] : convertMeta xs

-- TODO: Work out how qubit should be represented and do that
convertType :: HugrType -> M.Term
convertType HTQubit = M.Var "prelude.qubit"
convertType HTUSize = M.Var "prelude.usize"
--convertType HTArray = _
--convertType (HTSum sum) _
--convertType (HTOpaque ext typ args bound) = _
--convertType (HTFunc polyFuncType) = _
convertType x = error $ "convertType " ++ show x

convertValue :: HugrValue -> M.Term
convertValue (HVFunction hugr) = M.Func (convertHugr undefined hugr)
convertValue (HVTuple vs) = M.Tuple (M.Item . convertValue <$> vs)
convertValue hv@(HVExtension ext ty (CC tag cts)) = error $ show hv

convertSig :: FunctionType -> M.Term
convertSig fn@(FunctionType { .. }) = M.Apply "core.fn" [inpTm, outTm]
 where
  inpTm = M.List (M.Item . convertType <$> input)
  outTm = M.List (M.Item . convertType <$> output)

-- TODO: Rewrite this so that we don't rely on HugrGraph internals
hugrToModel :: HugrGraph -> Model M.Region
hugrToModel hg@(HugrGraph { ..  }) =
  case nodes Map.! root of
    OpDFG (DFG sig meta) -> dfgToRegion hg (root, sig, meta)
    _ -> error "TODO: Non-DFG root op"

-- Invariant: NodeId points to a DFG
dfgToRegion :: HugrGraph -> (NodeId, H.FunctionType, [(String, String)]) -> Model M.Region
dfgToRegion hg@(HugrGraph { ..  }) (nodeId, sig, meta) = do
  let [inp, out] = first_children Map.! nodeId
  sourceVars <- freshInputLinks nodeId (input sig)
  targetVars <- freshOutputLinks nodeId (output sig)
  for (zip [0..] sourceVars) $ \(ix, var) -> setInpVar inp [(ix, var)]
  for (zip [0..] targetVars) $ \(ix, var) -> setOutVar out [(ix, var)]
  let regionMetas = convertMeta meta
  let regionSignature = Just (convertSig sig)
  children <- traverse (convertNode hg)
              (delete inp $ delete out (getChildren hg root))
  pure (M.Region
       { sources = sourceVars
       , targets = targetVars
       , children = catMaybes children
       , regionMetas = regionMetas
       , regionSignature = regionSignature
       })

-- build a node and all of it's descendants
-- TODO: If nodes are deleted here, we need to keep a map of where the missing edges should end up
convertNode :: HugrGraph -> NodeId -> Model (Maybe M.Node)
convertNode hg nodeId = case nodes hg Map.! nodeId of
  (OpMod ModuleOp) -> pure Nothing -- Compilation should just produce hugrs, no modules
  -- We should write these edges to point to the parent
  (OpIn (InputNode tys meta)) -> error "Input node"
{-
                                       do
    let parent = getParent hg nodeId
    parentInputs <- getInpVars parent
    for (zip [0..] parentInputs) $ \(ix, link) -> setOutVar nodeId [(ix, link)]
    -- TODO: Something about metadata
    pure Nothing
-}
  (OpOut _) -> error "Output node"
{-  do
    let parent = getParent hg nodeId
    parentOutputs <- getOutVars parent
    for (zip [0..] parentOutputs) $ \(ix, link) -> setInpVar nodeId [(ix, link)]
    -- TODO: Something about metadata
    pure Nothing
-}
  (OpNoop _) -> pure Nothing
  -- TODO: Not making the child here? And associating it with the symbol?
  (OpDefn (FuncDefn name sig fmeta)) -> case getChildren hg nodeId of
    [bodyId] -> case nodes hg Map.! bodyId of
      -- TODO: Check the sigs are equal
      (OpDFG (DFG sig meta)) -> do
        reg <- dfgToRegion hg (bodyId, sig, meta)
        pure . Just $ M.Node
         { op = M.DefineFunc
                (M.Symbol (Just M.Public) name [] [] (convertSig sig))
         , inputs = []
         , outputs = []
         , regions = [reg]
         }
      x -> error $ "Non-dfg function " ++ show x
  (OpDFG (DFG sig meta)) -> do
    region <- dfgToRegion hg (nodeId, sig, meta)
    inWires <- for (inEdges hg nodeId) $ \(node, ix) -> do
      nodeEdges <- getCompiled (H.nodeId node)
      pure (fromJust (lookup ix nodeEdges))
    outWires <- for (outEdges hg nodeId) $ \(ix, node) -> do
      nodeEdges <- getCompiled (H.nodeId node)
      pure (fromJust (lookup ix nodeEdges))
    pure (Just (M.Node
         { op = M.Dfg
         , inputs = inWires
         , outputs = outWires
         , regions = [region]
         , nodeMetas = []
         , nodeSignature = M.regionSignature region
         }))
{-
convertOp hg (OpConst (ConstOp hv)) = convertValue hv
convertOp hg (OpConditional Conditional
convertOp hg (OpCase Case
convertOp hg (OpTag TagOp
convertOp hg (OpMakeTuple MakeTupleOp
convertOp hg (OpCustom CustomOp
convertOp hg (OpCall CallOp
convertOp hg (OpCallIndirect CallIndirectOp
convertOp hg (OpLoadConstant LoadConstantOp
convertOp hg (OpLoadFunction LoadFunctionOp
-}

-- Maybe this could be unified with hugrToModel?
convertHugr :: M.Term -> Hugr a -> M.Region
convertHugr = undefined


{- TODO: Ditch BS, encode bytes in Doc?

-- Magic prefix for encoded hugr that says it's uncompressed text
magic :: Builder
magic = "HUGRiHJv(" <> word8 64

printPackage :: HugrGraph -> Builder
printPackage hg = "(hugr 0)\n(mod)" <> (M.serialise hugrToModel)
-}

toModelString :: Namespace -> HugrGraph -> String
toModelString ns hg = M.printDoc (M.serialise (evalState (hugrToModel hg) (State ns Map.empty)))
