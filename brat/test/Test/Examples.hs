module Test.Examples (getExamplesTests) where

import Test.Checking (parseAndCheckNamed)
import Test.Compile.Hugr (compileToOutput)
import Brat.Load (parseFile)
import Brat.Machine (runInterpreter)

import Data.Char (isAlphaNum)
import Data.Functor ((<&>))
import Data.List (isPrefixOf)
import qualified Data.Text.Lazy as T
import Data.Maybe (fromJust)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Silver
import Test.Tasty.ExpectedFailure

--import Debug.Trace

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
                  -- testLine begins with execTestPrefix, then either " " or "-xfail " and the expected result
                  restLine = fromJust $ T.stripPrefix execTestPrefix testLine
                  (is_xfail, eOut) = case T.stripPrefix (T.pack "-xfail ") restLine of
                    Just out -> (True, out)
                    Nothing -> case T.stripPrefix (T.pack " ") restLine of
                      Just out -> (False, out)
                      Nothing -> error "Invalid test line, should start with '--!exec[-xfail] '"
                  expectedOutput = interpreterOutputPrefix ++ T.unpack (T.strip eOut)
                  -- this repeats/roughly duplicates the logic for "identifiers" in the parser
                  func_name = T.unpack $ T.takeWhile (\c -> isAlphaNum c || c == '_' || c == '\'') (T.drop 1 newlineDefn)
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
