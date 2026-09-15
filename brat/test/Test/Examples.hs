module Test.Examples (getExamplesTests) where

import Test.Checking (parseAndCheckNamed)
import Brat.Checker.Types (Modey(Kerny), VEnv)
import Brat.Compiler (compileToGraph, CompilingHoles(..))
import Brat.Compile.Hugr (compileKernel)
import Brat.Graph(Graph, Node(BratNode), NodeType(Box, Id))
import Brat.Load (parseFile)
import Brat.Machine (interpretGraph)
import Brat.Naming (Name)
import Brat.Syntax.Port  (NamedPort(..), OutPort(..), InPort(..))
import Brat.QualName (QualName)
import Brat.Syntax.Value (Val(VFun))

import Control.Exception (evaluate)
import Control.Monad (forM)
import qualified Data.ByteString as BS
import Data.Char (isAlphaNum)
import Data.Functor ((<&>))
import Data.Hugr (isHole)
import Data.HugrGraph as HG
import Data.List (isPrefixOf, sort)
import qualified Data.Text.Lazy as T
import Data.Maybe (fromJust, isJust)
import qualified Data.Map as M
import System.Directory (createDirectoryIfMissing)
import System.FilePath
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Silver
import Test.Tasty.ExpectedFailure


--import Debug.Trace

outputDir :: FilePath
outputDir = "test" </> "examples"

execTestPrefix :: T.Text
execTestPrefix = T.pack "--!exec"

interpreterOutputPrefix :: String
interpreterOutputPrefix = "Finished "


-- Map from box name to (compiled hugr, list of hole nodes in it)
type CompilationResult = M.Map Name (HG.HugrGraph HG.NodeId, [HG.NodeId])

compileFile :: [FilePath] -> String -> IO (Either CompilingHoles CompilationResult)
compileFile libDirs file = do
  (newRoot, (declEnv, holes, st, outerGraph, _)) <- compileToGraph libDirs file
  let venv = M.map fst declEnv
  case holes of
    [] -> let box_decls = (M.keys declEnv) >>= (findBoxes venv outerGraph)
          in Right <$> (evaluate -- turns 'error' into IO 'die'
            $ M.fromList [(n, let (hugr, holes) = compileKernel (newRoot, st, outerGraph) "root" n
                               in (hugr, map fst holes))
                         | n <- box_decls])
    hs -> pure $ Left (CompilingHoles hs)
 where
  findBoxes :: VEnv -> Graph -> QualName -> [Name]
  findBoxes venv (ns, es) name = case M.lookup name venv of
        Nothing -> error $ (show name) ++ ".... not found in VEnv"
        Just vals -> vals >>= \(NamedPort (Ex n _) _, _) -> case M.lookup n ns of
            Just (BratNode Id _ _) ->
               [src | (Ex src 0, _, In tgt _) <- es, tgt == n, isKernelBox src ns]
            _ -> []
  isKernelBox :: Name -> M.Map Name Node -> Bool
  isKernelBox name ns
    | Just (BratNode (Box _ _ ) [] [(_, VFun Kerny _cty)]) <- M.lookup name ns = True
    | otherwise = False

data FunctionTestType = SaveHugr | XfailOutput T.Text | Output T.Text

-- Note this completely recompiles the file for each test, which is pretty bad
funcTest :: String -> String -> FunctionTestType -> TestTree
funcTest path func_name testTy = case testTy of
  SaveHugr -> testCaseInfo func_name $ do
        let outFile = outputDir </> dropExtension (takeFileName path) ++ "_" ++ func_name <.> "json"
        hugr <- runInterpreter [] path func_name >>= \case
          Left s -> assertFailure $ "Expected hugr, got " ++ T.unpack s
          Right hugr -> pure hugr
        getHoles hugr @?= []
        -- output the hugr for validation
        createDirectoryIfMissing False outputDir
        BS.writeFile outFile $! (BS.toStrict $ HG.to_json hugr)
        pure $ "Written hugr to " ++ outFile ++ " pending validation"
  XfailOutput expectedOutput -> expectFail (funcTest path func_name (Output expectedOutput))
  Output out -> let expectedOutput = interpreterOutputPrefix ++ T.unpack (T.strip out)
                in testCase func_name $ runInterpreter [] path func_name >>= \case
      Left t -> T.unpack t @?= expectedOutput
      Right _ -> assertFailure $ "Expected output: '" ++ expectedOutput ++ "' but got a hugr!"
 where
  runInterpreter :: [FilePath] -> String -> String -> IO (Either T.Text (HG.HugrGraph HG.NodeId))
  runInterpreter libDirs file runFunc = compileToGraph libDirs file <&> \c -> interpretGraph c runFunc

compilePrefix = "test/compilation"
compileOutputDir = compilePrefix </> "output"

getExamplesTests :: IO TestTree
getExamplesTests =  do
  paths <- findByExtension [".brat"] "examples"
  testGroup "examples" <$> mapM (\path -> readFile path <&> mkTest path) paths
 where
  mkTest :: String -> String -> TestTree
  mkTest path cts =
    if isPrefixOf "--!xfail-parsing" cts then
      testGroup (show path) [expectFail parseTest]
    else if isPrefixOf "--!xfail-checking" cts then
      testGroup (show path) [parseTest, expectFail checkTest]
    else case interpreterTests of
      [] -> testGroup (show path) checkAndCompile
      intTests -> sequentialTestGroup path AllSucceed
          (checkAndCompile ++ [testGroup "execution" intTests])
   where
    parseTest = testCase "parsing" $ do
      case parseFile path cts of
        Left err -> assertFailure (show err)
        Right _ -> return () -- OK
    checkTest = parseAndCheckNamed "checking" [] path
    compileTest = testCaseInfo "compilation" $ do
      createDirectoryIfMissing False compileOutputDir
      compileFile [] path >>= \case
          Right hs -> mconcat <$> (forM (M.toList hs) $ \(boxName, (hugr, holes)) -> do
              sort (getHoles hugr) @?= sort holes
              -- ignore splices for now
              let outFile = compileOutputDir </> replaceExtension (takeFileName path) ((show boxName) ++ ".json")
              -- lots of fun with lazy and even strict bytestrings
              -- returning many bytes before evaluation has completed
              BS.writeFile outFile $! (BS.toStrict $ HG.to_json hugr)
              pure $ "Written to " ++ outFile ++ " pending validation\n")
          Left (CompilingHoles _) -> pure "Skipped as contains holes"
    
    checkAndCompile = if isPrefixOf "--!xfail-compilation" cts
      then [checkTest, expectFail compileTest] else [compileTest]
    interpreterTests = T.breakOnAll execTestPrefix (T.pack cts) <&> \(_, start) ->
      let (testLine, newlineDefn) = T.breakOn (T.pack "\n") start
          -- this repeats/roughly duplicates the logic for "identifiers" in the parser
          func_name = T.unpack $ T.takeWhile (\c -> isAlphaNum c || c == '_' || c == '\'') (T.drop 1 newlineDefn)
          -- testLine begins with execTestPrefix, then either
          -- " " and the expected result
          -- "-xfail " and the (un-)expected result
          -- "-hugr\n" (checks no splices, outputs hugr for validation)
          restLine = fromJust $ T.stripPrefix execTestPrefix testLine
      in case restLine of
           _ | (T.pack "-hugr") == restLine -> funcTest path func_name SaveHugr
           _ | Just out <- T.stripPrefix (T.pack "-xfail ") restLine ->
                  funcTest path func_name (XfailOutput out)
             | Just out <- T.stripPrefix (T.pack " ") restLine ->
                  funcTest path func_name (Output out)
             | otherwise -> error $ "Invalid exec test line: " ++ T.unpack testLine

getHoles :: Ord a => HugrGraph a -> [a]
getHoles hg = [n | n <- getNodes hg, isJust (isHole $ getOp hg n)]
