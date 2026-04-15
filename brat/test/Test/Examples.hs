module Test.Examples (getExamplesTests) where

import Test.Checking (parseAndCheck)
import Test.Compile.Hugr (compileToOutput)
import Brat.Load
import Brat.Machine (runInterpreter)

import Control.Exception
import Control.Monad (foldM)
import Data.Char (isAlphaNum)
import Data.Functor ((<&>))
import Data.List (isPrefixOf)
import qualified Data.Text as T
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Silver
import Test.Tasty.Silver.Advanced (goldenTest)
import Test.Tasty.ExpectedFailure
import System.Exit (ExitCode(..), die)
import System.IO
import System.IO.Silently

--import Debug.Trace

data Tests = Tests
  { parseTests :: [TestTree]
  , checkTests :: [TestTree]
  , compileTests :: [TestTree]
  , executionTests :: [TestTree]
  }


execTestPrefix :: T.Text
execTestPrefix = T.pack "--!test "

interpreterOutputPrefix :: String
interpreterOutputPrefix = "Finished "

getExamplesTests :: IO TestTree
getExamplesTests =  do
  paths <- findByExtension [".brat"] "examples"
  ts <- foldM addTests (Tests [] [] [] []) paths
  pure $ testGroup "examples" [
      testGroup "parsing" (parseTests ts),
      testGroup "checking" (checkTests ts),
      testGroup "compilation" (compileTests ts),
      testGroup "execution" (executionTests ts)
    ]
 where
  addTests :: Tests -> FilePath -> IO Tests
  addTests tests@Tests{..} path = readFile path <&> \cts ->
    let parseTest = testCase (show path) $ do
          case parseFile path cts of
            Left err -> assertFailure (show err)
            Right _ -> return () -- OK
        checkTest = parseAndCheck [] path
        compileTest = compileToOutput path
    in if isPrefixOf "--!xfail-parsing" cts then
      tests { parseTests = (expectFail parseTest):parseTests }
    else if isPrefixOf "--!xfail-checking" cts then
      tests { parseTests = parseTest:parseTests, checkTests = (expectFail checkTest):checkTests }
    else if isPrefixOf "--!xfail-compilation" cts then
      tests { checkTests = checkTest:checkTests, compileTests = (expectFail compileTest):compileTests }
    else
      let interpreterTests = T.breakOnAll execTestPrefix (T.pack cts) <&> \(_, start) ->
            let (testLine, newlineDefn) = T.breakOn (T.pack "\n") start
                expectedOutput = interpreterOutputPrefix ++ T.unpack (T.drop (T.length execTestPrefix) testLine) ++ "\n"
                -- this repeats/roughly duplicates the logic for "identifiers" in the parser
                func_name = T.unpack $ T.takeWhile (\c -> isAlphaNum c || c == '_' || c == '\'') (T.drop 1 newlineDefn)
                -- this completely recompiles the file for each test, which is pretty bad
              in goldenVsText func_name (T.pack expectedOutput) (runInterpreter [] path func_name)
          testsWithCompile = tests {compileTests = compileTest:compileTests }
        in if length interpreterTests > 0 then
            testsWithCompile {executionTests = (testGroup path interpreterTests):executionTests}
          else testsWithCompile

runGetStderr :: IO () -> IO String
runGetStderr action = do
    (output, ()) <- hCapture [stdout, stderr] $
      action `catch` \(ExitFailure c) -> pure ()
    pure output

goldenVsText :: TestName -> T.Text -> IO () -> TestTree
goldenVsText name expected action =
  goldenTest name (pure expected) (runGetStderr action <&> T.pack) (do_diff)
    (\_ -> die "cannot update golden, must edit test")
 where
  do_diff :: T.Text -> T.Text -> IO (Maybe String)
  do_diff expected actual = pure $ if expected == actual then Nothing
    else Just $ "Expected: " ++ T.unpack expected ++ " Actual: " ++ T.unpack actual
