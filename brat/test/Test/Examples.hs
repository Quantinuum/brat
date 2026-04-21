module Test.Examples (getExamplesTests) where

import Test.Checking (parseAndCheckNamed)
import Test.Compile.Hugr (compileToOutput, getSplices)
import Brat.Load (parseFile)
import Brat.Machine (runInterpreter)
import Data.HugrGraph (to_json)

import qualified Data.ByteString as BS
import Data.Char (isAlphaNum)
import Data.Functor ((<&>))
import Data.List (isPrefixOf)
import qualified Data.Text.Lazy as T
import Data.Maybe (fromJust)
import System.Directory (createDirectoryIfMissing)
import System.FilePath
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Silver
import Test.Tasty.ExpectedFailure

--import Debug.Trace

outputDir :: FilePath
outputDir = "test/examples/output"

execTestPrefix :: T.Text
execTestPrefix = T.pack "--!exec"

interpreterOutputPrefix :: String
interpreterOutputPrefix = "Finished "

getExamplesTests :: IO TestTree
getExamplesTests =  do
  paths <- findByExtension [".brat"] "examples"
  testGroup "examples" <$> mapM mkTest paths
 where
  mkTest :: FilePath -> IO TestTree
  mkTest path = readFile path <&> \cts ->
    let parseTest = testCase "parsing" $ do
          case parseFile path cts of
            Left err -> assertFailure (show err)
            Right _ -> return () -- OK
        checkTest = parseAndCheckNamed "checking" [] path
    in if isPrefixOf "--!xfail-parsing" cts then
         testGroup (show path) [expectFail parseTest]
       else if isPrefixOf "--!xfail-checking" cts then
         testGroup (show path) [parseTest, expectFail checkTest]
       else
        let interpreterTests = T.breakOnAll execTestPrefix (T.pack cts) <&> \(_, start) ->
              let (testLine, newlineDefn) = T.breakOn (T.pack "\n") start
                  -- this repeats/roughly duplicates the logic for "identifiers" in the parser
                  func_name = T.unpack $ T.takeWhile (\c -> isAlphaNum c || c == '_' || c == '\'') (T.drop 1 newlineDefn)
                  -- testLine begins with execTestPrefix, then either
                  -- " " and the expected result
                  -- "-xfail " and the (un-)expected result
                  -- "-hugr\n" (checks no splices, outputs hugr for validation)
                  restLine = fromJust $ T.stripPrefix execTestPrefix testLine
              in if (T.pack "-hugr") == restLine then testCaseInfo func_name $ do
                let outFile = outputDir </> dropExtension (takeFileName path) ++ "_" ++ func_name <.> "json"
                -- this completely recompiles the file for each test, which is pretty bad
                hugr <- runInterpreter [] path func_name >>= \case
                  Left s -> assertFailure $ "Expected hugr, got " ++ T.unpack s
                  Right hugr -> pure hugr
                getSplices hugr @?= []
                -- output the hugr for validation
                createDirectoryIfMissing False outputDir
                BS.writeFile outFile $! (BS.toStrict $ to_json hugr)
                pure $ "Written hugr to " ++ outFile ++ " pending validation"
              else
                let (is_xfail, eOut) = case T.stripPrefix (T.pack "-xfail ") restLine of
                      Just out -> (True, out)
                      Nothing | Just out <- T.stripPrefix (T.pack " ") restLine -> (False, out)
                              | otherwise -> error $ "Invalid exec test line: " ++ T.unpack testLine
                    expectedOutput = interpreterOutputPrefix ++ T.unpack (T.strip eOut)
                in (if is_xfail then expectFail else id) $ testCase func_name $ do
                  -- this completely recompiles the file for each test, which is pretty bad
                  runInterpreter [] path func_name >>= \case
                    Left t -> T.unpack t @?= expectedOutput
                    Right _ -> assertFailure $ "Expected output: '" ++ expectedOutput ++ "' but got a hugr!"
            compileTest = compileToOutput "compilation" path
            checkAndCompile = if isPrefixOf "--!xfail-compilation" cts
              then [checkTest, expectFail compileTest] else [compileTest]
        in case interpreterTests of
          [] -> testGroup (show path) checkAndCompile
          intTests -> sequentialTestGroup path AllSucceed
              (checkAndCompile ++ [testGroup "execution" intTests])
