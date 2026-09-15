module Test.Examples (getExamplesTests) where

import Test.Checking (parseAndCheckNamed)
import Brat.Compiler (compileToGraph)
import Brat.Load (parseFile, VMod)
import Brat.Machine (interpretGraph)
import Brat.Naming (Namespace)

import Control.Exception (catch)
import qualified Data.ByteString as BS
import Data.Char (isAlphaNum)
import Data.Functor ((<&>))
import Data.Hugr (isHole)
import Data.HugrGraph as HG
import Data.List (isPrefixOf)
import qualified Data.Text.Lazy as T
import Data.Maybe (fromJust, isJust)
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

data FunctionTestType = SaveHugr | XfailOutput T.Text | Output T.Text

funcTest :: (Namespace, VMod) -> String -> String -> FunctionTestType -> TestTree
funcTest nsmod path func_name testTy = case testTy of
  SaveHugr -> testCaseInfo func_name $ do
        hugr <- case interpretGraph nsmod func_name of
              Left s -> assertFailure $ "Expected hugr, got " ++ T.unpack s
              Right hugr -> pure hugr
        getHoles hugr @?= []
        -- output the hugr for validation
        let outFile = outputDir </> dropExtension (takeFileName path) ++ "_" ++ func_name <.> "json"
        createDirectoryIfMissing False outputDir
        BS.writeFile outFile $! (BS.toStrict $ HG.to_json hugr)
        pure $ "Written hugr to " ++ outFile ++ " pending validation"
  XfailOutput expectedOutput -> expectFail (funcTest nsmod path func_name (Output expectedOutput))
  Output out -> let expectedOutput = interpreterOutputPrefix ++ T.unpack (T.strip out)
                in testCase func_name $ case interpretGraph nsmod func_name of
      Left t -> T.unpack t @?= expectedOutput
      Right _ -> assertFailure $ "Expected output: '" ++ expectedOutput ++ "' but got a hugr!"

compilePrefix = "test/compilation"
compileOutputDir = compilePrefix </> "output"

getExamplesTests :: IO TestTree
getExamplesTests =  do
  paths <- findByExtension [".brat"] "examples"
  testGroup "examples" <$> mapM (\path -> readFile path >>= mkTest path) paths
 where
  mkTest :: String -> String -> IO TestTree
  mkTest path cts =
    if isPrefixOf "--!xfail-parsing" cts then
      pure $ testGroup (show path) [expectFail parseTest]
    else if isPrefixOf "--!xfail-checking" cts then
      pure $ testGroup (show path) [parseTest, expectFail checkTest]
    else do
      maybe_mod <- catch (compileToGraph [] path <&> Just) (\(e :: IOError) -> pure Nothing)
      let interpreterTests = case maybe_mod of
            Nothing -> [testCaseInfo "execution" $ pure "SKIPPED as did not compile"]
            Just nsmod -> findInterpreterTests nsmod
      pure $ case interpreterTests of
        [] -> testGroup (show path) [checkTest]
        intTests -> sequentialTestGroup path AllSucceed
            (checkTest:[testGroup "execution" intTests])
   where
    parseTest = testCase "parsing" $ do
      case parseFile path cts of
        Left err -> assertFailure (show err)
        Right _ -> return () -- OK
    checkTest = parseAndCheckNamed "checking" [] path
    findInterpreterTests :: (Namespace, VMod) -> [TestTree]
    findInterpreterTests nsmod = T.breakOnAll execTestPrefix (T.pack cts) <&> \(_, start) ->
      let (testLine, newlineDefn) = T.breakOn (T.pack "\n") start
          -- this repeats/roughly duplicates the logic for "identifiers" in the parser
          func_name = T.unpack $ T.takeWhile (\c -> isAlphaNum c || c == '_' || c == '\'') (T.drop 1 newlineDefn)
          -- testLine begins with execTestPrefix, then either
          -- " " and the expected result
          -- "-xfail " and the (un-)expected result
          -- "-hugr\n" (checks no splices, outputs hugr for validation)
          restLine = fromJust $ T.stripPrefix execTestPrefix testLine
      in case restLine of
           _ | (T.pack "-hugr") == restLine -> funcTest nsmod path func_name SaveHugr
           _ | Just out <- T.stripPrefix (T.pack "-xfail ") restLine ->
                  funcTest nsmod path func_name (XfailOutput out)
             | Just out <- T.stripPrefix (T.pack " ") restLine ->
                  funcTest nsmod path func_name (Output out)
             | otherwise -> error $ "Invalid exec test line: " ++ T.unpack testLine

getHoles :: Ord a => HugrGraph a -> [a]
getHoles hg = [n | n <- getNodes hg, isJust (isHole $ getOp hg n)]
