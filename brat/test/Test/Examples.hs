module Test.Examples (getExamplesTests) where

import Test.Checking (parseAndCheck)
import Test.Compile.Hugr (compileToOutput)
import Brat.Load

import Control.Monad (foldM)
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

getExamplesTests :: IO TestTree
getExamplesTests =  do
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
