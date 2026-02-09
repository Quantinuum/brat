-- Module for printing out a HugrGraph as a hugr model
module Brat.Compile.Model where

import Control.Monad.State
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.ByteString.Builder (Builder, word8)
import qualified Data.Map as Map

import Brat.Naming (Name, Namespace, fresh)
import Data.Hugr
import Data.HugrGraph
import qualified Data.Hugr.Model as M

data ModelState = State
 { ns :: Namespace
 , compiled :: Map.Map NodeId [(Int, M.Term)]

type Model = State (Namespace, Map.Map NodeId [(Int, M.Term)]) -- out nodes that have been compiled

freshName :: Model Name
freshName = do
  (ns, edgeMap) <- get
  let (name, ns') = fresh "" ns
  put (ns', edgeMap)
  pure name

freshNames :: [a] -> Model [Name]
freshNames [] = pure []
freshNames (_:xs) = (:) <$> freshName <*> freshNames xs

convertMeta :: [(String, String)] -> [M.Term]
convertMeta [] = []
convertMeta ((key,val):xs) = M.Tuple [M.Item (M.Literal (M.LitStr key)), M.Item (M.LitStr key)] : convertMeta xs

-- TODO: Work out how qubit should be represented and do that
convertType :: HugrType -> M.Term
convertType x = error $ "convertType " ++ show x

convertValue :: HugrValue -> M.Term
convertValue (HVFunction hugr) = M.Func (convertHugr hugr)
convertValue (HVTuple vs) = M.Tuple (M.Item . convertValue <$> vs)
convertValue hv@(HVExtension ext ty (CC tag cts)) = error $ show hv

convertSig :: FunctionType -> M.Term
convertSig (FunctionType { .. }) = M.Apply "core.fn" [inpTm, outTm]
 where
  inpTm = M.List (M.Item . convertType <$> M.inputs)
  outTm = M.List (M.Item . convertType <$> M.outputs)

-- TODO: Rewrite this so that we don't rely on HugrGraph internals
hugrToModel :: HugrGraph -> Model M.Region
hugrToModel hg@(HugrGraph { ..  }) = do
  (op, sig, meta) <- pure $ case nodes Map.! root of
    OpDFG (DFG sig meta) -> (DFG, sig, meta)
    _ -> error "TODO: Non-DFG root op"
  let [inp, out] = first_children Map.! root
  let sources = freshNames (input sig)
  let targets = freshNames (output sig)
  let regionMetas = convertMeta meta
  let regionSignature = Just (convertSig sig)
  children <- traverse (convertNode hg)
              (Map.keys $ Map.filter (== root) (Map.delete inp $ Map.delete out (parents hg)))
  pure (M.Region { .. })

-- build a node and all of it's descendants
-- TODO: If nodes are deleted here, we need to keep a map of where the missing edges should end up
convertNode :: HugrGraph -> NodeId -> Model M.Node
convertNode hg nodeId = case nodes hg Map.! nodeId of
  (OpMod ModuleOp) -> Nothing -- Compilation should just produce hugrs, no modules
  (OpIn _) -> Nothing -- We should read input and output nodes seperately
  (OpOut _) -> Nothing
  (OpNoop _) -> Nothing
  -- TODO: Not making the child here? And associating it with the symbol?
  (OpDefn (FuncDefn name sig _meta)) -> case getChildren hg of
    [body] -> do
      reg <- dfgToRegion body
      pure $ M.Node
       { op = M.DefineFunc (M.Symbol (Just M.Public)) name [] [] (convertSig sig)
       , inputs = []
       , outputs = []
       , regions = reg
       }
convertOp hg (OpDFG (DFG sig meta)) = undefined
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

dfgToRegion :: (NodeId, M.Term, [(String, String)]) -> Model M.Region
dfgToRegion (nodeId, sig, meta) = case nodes hg Map.! nodeId of
  (OpDFG (Dfg sig meta)) -> _
  _ -> error "Not a dfg"

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
