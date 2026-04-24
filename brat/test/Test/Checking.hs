module Test.Checking (parseAndCheck, parseAndCheckNamed) where

import Brat.Load
import Brat.Naming (root)

import Control.Monad.Except
import Test.Tasty
import Test.Tasty.HUnit

parseAndCheck :: [FilePath] -> FilePath -> TestTree
parseAndCheck libDirs file = parseAndCheckNamed (show file) libDirs file

parseAndCheckNamed :: String -> [FilePath] -> FilePath -> TestTree
parseAndCheckNamed name libDirs file = testCase name $ do
  env <- runExceptT $ loadFilename root libDirs file
  case env of
    Left err -> assertFailure (show err)
    Right (declEnv, holes, _, _, _) ->
      (length declEnv + length holes > 0) @? "Should produce something"
