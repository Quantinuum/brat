-- Module for printing out a HugrGraph as a hugr model
module Brat.Compile.Model (toModelString, toModelEnvelope) where

import Control.Monad.State
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.ByteString.Builder (Builder, word8)
import Data.Traversable (for)
import Data.List (delete)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, fromJust, fromMaybe)

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
--setOutVar key val | trace ("setOutVar " ++ show key ++ " " ++ show val) False = undefined
setOutVar key val = do
  ms <- get
  let newVal = case Map.lookup key (outVars ms) of
        Just orig -> Map.toList (Map.union (Map.fromList val) (Map.fromList orig))
        Nothing -> val
  put (ms { outVars = Map.insert key newVal (outVars ms) })

setInpVar :: NodeId -> [(Int, M.LinkName)] -> Model ()
--setInpVar key val | trace ("setInpVar " ++ show key ++ " " ++ show val) False = undefined
setInpVar key val = do
  ms <- get
  let newVal = case Map.lookup key (inpVars ms) of
        Just orig -> Map.toList (Map.union (Map.fromList val) (Map.fromList orig))
        Nothing -> val
  put (ms { inpVars = Map.insert key newVal (inpVars ms) })

-- The thing had better be defined!
-- TODO: Allow it not to be?
getInpVars :: NodeId -> Model [(Int, M.LinkName)]
getInpVars nid = gets (fromMaybe [] . (Map.lookup nid) . inpVars)

getOutVars :: NodeId -> Model [(Int, M.LinkName)]
getOutVars nid = gets (fromMaybe [] . (Map.lookup nid) . outVars)

getDangling :: NodeId -> Int -> Model (Maybe M.LinkName)
getDangling nid port = do
  vars <- getOutVars nid
  pure (lookup port vars)

getHungry :: NodeId -> Int -> Model (Maybe M.LinkName)
getHungry nid port = do
  vars <- getInpVars nid
  pure (lookup port vars)

freshName :: Model Name
freshName = do
  st <- get
  let (name, ns') = fresh (show (nameCount st)) (ns st)
  put (st { ns = ns', nameCount = nameCount st + 1 })
  pure name

makeInputLink :: NodeId -> Int -> Model M.LinkName
makeInputLink nid port = do
  name <- freshName
  let link = '%':show name
  setInpVar nid [(port, ('%':show name))]
  pure link

makeOutputLink :: NodeId -> Int -> Model M.LinkName
makeOutputLink nid port = do
  name <- freshName
  let link = '%':show name
  setOutVar nid [(port, ('%':show name))]
  pure link

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
convertType (HTSum (SU (UnitSum n))) = M.Apply "core.adt" [M.List [M.Item (M.List []) | _ <- [1..n]]]
convertType (HTSum (SG (GeneralSum rows))) = M.Apply "core.adt" [M.List [ M.Item (M.List (M.Item . convertType <$> row)) | row <- rows ]]
--convertType (HTOpaque ext typ args bound) = _
--convertType (HTFunc polyFuncType) = _
convertType x = error $ "convertType " ++ show x

convertValue :: HugrValue -> M.Term
-- convertValue (HVFunction hugr) = undefined
convertValue (HVTuple vs) = M.Tuple (M.Item . convertValue <$> vs)
convertValue hv@(HVExtension ext ty (CC tag cts)) = error $ show hv

convertSig :: FunctionType -> M.Term
convertSig fn@(FunctionType { .. }) = M.Apply "core.fn" [inpTm, outTm]
 where
  inpTm = M.List (M.Item . convertType <$> input)
  outTm = M.List (M.Item . convertType <$> output)

-- TODO: Rewrite this so that we don't rely on HugrGraph internals
hugrToModel :: HugrGraph NodeId -> Model M.Package
hugrToModel hg@(HugrGraph { ..  }) =
  case getOp hg root of
    OpDFG (DFG sig meta) -> M.H <$> dfgToRegion hg (root, sig, meta)
    _ -> error "TODO: Non-DFG root op"

-- Invariant: NodeId points to a DFG
dfgToRegion :: HugrGraph -> (NodeId, H.FunctionType, [(String, String)]) -> Model M.Region
dfgToRegion hg@(HugrGraph { ..  }) (nodeId, sig, meta) = do
  let [inp, out] = fromMaybe (error "no kids") $ Map.lookup nodeId first_children
  sourceVars <- freshOutputLinks inp (input sig)
  targetVars <- freshInputLinks out (output sig)
  let regionMetas = convertMeta meta
  let regionSignature = Just (convertSig sig)
  children <- traverse (convertNode hg)
              (delete inp $ delete out (getChildren hg nodeId))
  pure (M.Region
       { kind = M.DFG
       , sources = sourceVars
       , targets = targetVars
       , children = catMaybes children
       , regionMetas = regionMetas
       , regionSignature = regionSignature
       })

-- Get the links corresponding to the inputs and outputs of a Model Node
nodeInputs :: HugrGraph -> NodeId -> Model [M.LinkName] -- inputs
nodeInputs hg nodeId =
  for (inEdges hg nodeId) $ \(Port srcNode srcIx, tgtIx) -> do
    getDangling srcNode srcIx >>= \case
      Just link -> pure link
      Nothing -> makeInputLink nodeId tgtIx

nodeOutputs :: HugrGraph -> NodeId -> Model [M.LinkName]
nodeOutputs hg nodeId =
  for (outEdges hg nodeId) $ \(srcIx, Port tgtNode tgtIx) -> do
    getHungry tgtNode tgtIx >>= \case
      Just link -> pure link
      Nothing -> makeOutputLink nodeId srcIx


-- build a node and all of it's descendants
-- TODO: If nodes are deleted here, we need to keep a map of where the missing edges should end up
convertNode :: HugrGraph -> NodeId -> Model (Maybe M.Node)
convertNode hg nodeId = case getOp hg nodeId of
  (OpMod ModuleOp) -> pure Nothing -- Compilation should just produce hugrs, no modules
  -- We should write these edges to point to the parent
  (OpIn (InputNode tys meta)) -> error $ "Input node with parent " -- ++ show (getOp hg (getParent hg nodeId))
  (OpOut _) -> error "Output node"
  (OpCase _) -> error "Case node"
  (OpNoop _) -> pure Nothing
  -- TODO: Not making the child here? And associating it with the symbol?
  (OpDefn (FuncDefn name sig fmeta)) -> case getChildren hg nodeId of
    [bodyId] -> case getOp hg bodyId of
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
    inWires <- if null (input sig) then pure [] else nodeInputs hg nodeId
    outWires <- nodeOutputs hg nodeId
    region <- dfgToRegion hg (nodeId, sig, meta)
    pure (Just (M.Node
         { op = M.Dfg
         , inputs = inWires
         , outputs = outWires
         , regions = [region]
         , nodeMetas = []
         , nodeSignature = M.regionSignature region
         }))
  (OpConditional (Conditional { .. })) -> do
    inWires <- nodeInputs hg nodeId
    outWires <- nodeOutputs hg nodeId

    let discrim = M.Apply "core.adt" [M.List [M.Item (M.List (M.Item . convertType <$> row)) | row <- sum_rows ]]
    let signature = M.Apply "core.fn"
                    [M.List (M.Item discrim : [M.Item (convertType ty) | ty <- other_inputs])
                    ,M.List [M.Item (convertType ty) | ty <- outputs ++ other_inputs]
                    ]

    -- All of the children should be case nodes
    regions <- for (getChildren hg nodeId) $ \caseId -> case getOp hg caseId of
      (OpCase (Case sig meta)) -> dfgToRegion hg (caseId, sig, meta)
      x -> error ("Non case child of conditional: " ++ show x)

    pure (Just (M.Node
         { op = M.Conditional
         , inputs = inWires
         , outputs = outWires
         , regions = regions
         , nodeMetas = []
         , nodeSignature = Just signature
         }))

  (OpTag (TagOp tag sumTy meta)) -> do
    inWires <- if null (sumTy !! tag) then pure [] else nodeInputs hg nodeId
    outWires <- nodeOutputs hg nodeId
    let op = M.Custom (M.Apply "core.make_adt" [M.Literal (M.LitNat tag)])
    let inTys = M.List (M.Item . convertType <$> sumTy !! tag)
    let outTy = M.Apply "core.adt" [M.List [ M.Item (M.List (M.Item . convertType <$> row)) | row <- sumTy] ]
    let signature = M.Apply "core.fn" [inTys, outTy]
    pure (Just (M.Node
         { op = op
         , inputs = inWires
         , outputs = outWires
         , regions = []
         , nodeMetas = []
         , nodeSignature = Just signature
         }))
  (OpCustom (CustomOp ext op sig args)) -> do
    inWires <- if null (input sig) then pure [] else nodeInputs hg nodeId
    outWires <- nodeOutputs hg nodeId
    pure (Just (M.Node
         { op = M.Custom (M.Apply (ext ++ "." ++ op) [])
         , inputs = inWires
         , outputs = outWires
         , regions = []
         , nodeMetas = []
         , nodeSignature = Just (convertSig sig)
         }))

{-
convertOp hg (OpConst (ConstOp hv)) = convertValue hv
convertOp hg (OpMakeTuple MakeTupleOp
convertOp hg (OpCustom CustomOp
convertOp hg (OpCall CallOp
convertOp hg (OpCallIndirect CallIndirectOp
convertOp hg (OpLoadConstant LoadConstantOp
convertOp hg (OpLoadFunction LoadFunctionOp
-}



{- TODO: Ditch BS, encode bytes in Doc?

-- Magic prefix for encoded hugr that says it's uncompressed text
magic :: Builder
magic = "HUGRiHJv(" <> word8 64

printPackage :: HugrGraph -> Builder
printPackage hg = "(hugr 0)\n(mod)" <> (M.serialise hugrToModel)
-}

toModelString :: Namespace -> HugrGraph -> String
toModelString ns hg = M.printDoc (M.serialise (evalState (hugrToModel hg) (State ns 0 Map.empty Map.empty)))

magic = "HUGRiHJv(@"

toModelEnvelope :: Namespace -> HugrGraph NodeId -> String
toModelEnvelope ns hg = magic ++ M.printDoc (M.serialise (evalState (hugrToModel hg) (State ns 0 Map.empty Map.empty)))
