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
getSpliceTests = do
  createDirectoryIfMissing True outputDir
  pure $ testGroup "splice" [testSplice False, testSplice True]

testSplice :: Bool -> TestTree
testSplice inline = testCaseInfo name $ do
  let (h, holeId) = host
  let outPrefix = outputDir </> name
  BS.writeFile (outPrefix ++ "_host.json") (encode $ H.serialize h)
  BS.writeFile (outPrefix ++ "_insertee.json") (encode $ H.serialize dfgHugr)
  let spliced = H.splice h holeId dfgHugr
  let resHugr@(Hugr (ns, _))  = H.serialize $ if inline
        then execState (inlineDFG holeId) spliced else spliced
  let outFile = outPrefix ++ "_result.json"
  BS.writeFile outFile $ encode resHugr
  assertBool "Should be no holes now" $ isNothing $ find (isJust . isHole) $ snd <$> ns
  -- if inline, we should assert there's no DFG either
  pure $ "Written to " ++ outFile ++ " pending validation"
 where
  name = if inline then "inline" else "noinline"
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
