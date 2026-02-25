module Test.HugrGraph(getSpliceTests) where

import Brat.Naming as N
import Data.HugrGraph as H
import Data.Hugr

import Control.Monad.State (State, execState, get, runState, modify, state)
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

addNode :: String -> NodeId -> HugrOp -> State (HugrGraph NodeId, Namespace) NodeId
addNode nam parent op = do
  name <- H.freshNode parent nam
  modify $ \(h, ns) -> (execState (H.setOp name op) h, ns)
  pure name

getSpliceTests :: IO TestTree
getSpliceTests = do
  createDirectoryIfMissing True outputDir
  pure $ testGroup "splice" [testSplice i p | i <- [False, True], p <- [False, True]]

testSplice :: Bool -> Bool -> TestTree
testSplice inline prepend = testCaseInfo name $ do
  let (holeId,(h, ns)) = host
  let outPrefix = outputDir </> name
  BS.writeFile (outPrefix ++ "_host.json") (encode $ H.serialize h)
  BS.writeFile (outPrefix ++ "_insertee.json") (encode $ H.serialize dfgHugr)
  let spliced = if prepend
                then execState (H.splice_prepend holeId dfgHugr) h
                else fst $ execState (H.splice_new holeId dfgHugr) (h, ns)
  let resHugr@(Hugr (ns, _))  = H.serialize $ if inline
        then execState (inlineDFG holeId) spliced else spliced
  let outFile = outPrefix ++ "_result.json"
  BS.writeFile outFile $ encode resHugr
  assertBool "Should be no holes now" $ isNothing $ find (isJust . isHole) $ snd <$> ns
  -- if inline, we should assert there's no DFG either
  pure $ "Written to " ++ outFile ++ " pending validation"
 where
  name = (if inline then "inline" else "noinline") ++ (if prepend then "_prepend" else "_new")
  host :: (NodeId, (HugrGraph NodeId, Namespace))
  host = flip runState (runState (H.new "root" rootDefn) N.root) $ do
    root <- get <&> H.root . fst
    input <- addNode "inp" root (OpIn (InputNode tys []))
    output <- addNode "out" root (OpOut (OutputNode tys []))
    jh $setFirstChildren root [input, output]
    hole <- addNode "hole" root (OpCustom $ holeOp 0 tq_ty)
    jh $ H.addEdge (Port input 0, Port hole 0)
    jh $ H.addEdge (Port input 1, Port hole 1)
    jh $ H.addEdge (Port hole 0, Port output 0)
    jh $ H.addEdge (Port hole 1, Port output 1)
    pure hole
  dfgHugr :: HugrGraph NodeId
  dfgHugr =
   let (initHugr, ns) = runState (H.new "root" rootDfg) N.root
   in fst $ flip execState (initHugr, ns) $ do
    root <- get <&> H.root . fst
    input <- addNode "inp" root (OpIn (InputNode tys []))
    output <- addNode "out" root (OpOut (OutputNode tys []))
    jh $ setFirstChildren root [input, output]
    gate <- addNode "gate" root (OpCustom $ CustomOp "tket" "CX" tq_ty [])
    jh $ H.addEdge (Port input 0, Port gate 0)
    jh $ H.addEdge (Port input 1, Port gate 1)
    jh $ H.addEdge (Port gate 0, Port output 0)
    jh $ H.addEdge (Port gate 1, Port output 1)
  swap (x,y) = (y,x)
  tys = [HTQubit, HTQubit]
  tq_ty = FunctionType tys tys bratExts
  rootDefn = OpDefn $ FuncDefn "main" (PolyFuncType [] tq_ty) []
  rootDfg = OpDFG $ DFG tq_ty []

jh :: State (HugrGraph NodeId) a -> State (HugrGraph NodeId, Namespace) a
jh action = state $ \ (h, ns) ->
  let (a, h') = runState action h in (a, (h', ns))