module Test.Checking (parseAndCheck, getCheckingTests) where

import Test.Compile.Hugr (compileToOutput)
import Brat.Load
import Brat.Naming (root)

import Control.Monad (foldM)
import Control.Monad.Except
import Data.Functor ((<&>))
import Data.List (isPrefixOf)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Silver
import Test.Tasty.ExpectedFailure

data Tests = Tests
  { parseTests :: [TestTree]
  , checkTests :: [TestTree]
  , compileTests :: [TestTree]
  }

getCheckingTests :: IO TestTree
getCheckingTests =  do
  paths <- findByExtension [".brat"] "examples"
  ts <- foldM addTests (Tests [] [] []) paths
  pure $ testGroup "examples" [
      testGroup "parsing" (parseTests ts),
      testGroup "checking" (checkTests ts),
      testGroup "compilation" (compileTests ts)
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
      tests { compileTests = compileTest:compileTests }

parseAndCheck :: [FilePath] -> FilePath -> TestTree
parseAndCheck libDirs file = testCase (show file) $ do
  env <- runExceptT $ loadFilename root libDirs file
  case env of
    Left err -> assertFailure (show err)
    Right (declEnv, holes, _, _, _) ->
      (length declEnv + length holes > 0) @? "Should produce something"
