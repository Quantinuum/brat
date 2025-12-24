module Test.HugrGraph(getSpliceTests) where

import Brat.Naming as N
import Data.HugrGraph as H
import Data.Hugr

import Control.Monad.State (State, execState, get, runState)
import Data.Aeson (encode)
import Data.Functor ((<&>))
import Data.Maybe (isJust, isNothing)
import Data.List (find)
import qualified Data.ByteString.Lazy as BS
import System.Directory (createDirectoryIfMissing)
import System.FilePath
import Test.Tasty
import Test.Tasty.HUnit

prefix = "test/hugr"
outputDir = prefix </> "output"

addNode :: String -> NodeId -> HugrOp -> State HugrGraph NodeId
addNode nam parent op = do
  name <- H.freshNode parent nam
  H.setOp name op
  pure name

getSpliceTests :: IO TestTree
getSpliceTests = createDirectoryIfMissing True outputDir >> pure testSplice

testSplice :: TestTree
testSplice = testCaseInfo "splice" $ do
  let (h, holeId) = host
  BS.writeFile (outputDir </> "host.json") (encode $ H.serialize h)
  BS.writeFile (outputDir </> "insertee.json") (encode $ H.serialize dfgHugr)
  let resHugr@(Hugr (ns, _))  = H.serialize $ H.splice h holeId dfgHugr
  let outFile = outputDir </> "result.json"
  BS.writeFile outFile $ encode resHugr
  assertBool "Should be no holes now" $ isNothing $ find (isJust . isHole) $ snd <$> ns
  pure $ "Written to " ++ outFile ++ " pending validation"
 where
  host :: (HugrGraph, NodeId)
  host = swap $ flip runState (H.new N.root "root" rootDefn) $ do
    root <- get <&> H.root
    input <- addNode "inp" root (OpIn (InputNode tys []))
    output <- addNode "out" root (OpOut (OutputNode tys []))
    setFirstChildren root [input, output]
    hole <- addNode "hole" root (OpCustom $ holeOp 0 tq_ty)
    H.addEdge (Port input 0, Port hole 0)
    H.addEdge (Port input 1, Port hole 1)
    H.addEdge (Port hole 0, Port output 0)
    H.addEdge (Port hole 1, Port output 1)
    pure hole
  dfgHugr :: HugrGraph
  dfgHugr = flip execState (H.new N.root "root" rootDfg) $ do
    root <- get <&> H.root
    input <- addNode "inp" root (OpIn (InputNode tys []))
    output <- addNode "out" root (OpOut (OutputNode tys []))
    setFirstChildren root [input, output]
    gate <- addNode "gate" root (OpCustom $ CustomOp "tket" "CX" tq_ty [])
    H.addEdge (Port input 0, Port gate 0)
    H.addEdge (Port input 1, Port gate 1)
    H.addEdge (Port gate 0, Port output 0)
    H.addEdge (Port gate 1, Port output 1)
  swap (x,y) = (y,x)
  tys = [HTQubit, HTQubit]
  tq_ty = FunctionType tys tys bratExts
  rootDefn = OpDefn $ FuncDefn "main" (PolyFuncType [] tq_ty) []
  rootDfg = OpDFG $ DFG tq_ty []
