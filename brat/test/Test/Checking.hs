module Test.Checking (parseAndCheck) where

import Brat.Load
import Brat.Naming (root)

import Control.Monad.Except
import Test.Tasty
import Test.Tasty.HUnit

parseAndCheck :: [FilePath] -> FilePath -> TestTree
parseAndCheck libDirs file = testCase (show file) $ do
  env <- runExceptT $ loadFilename root libDirs file
  case env of
    Left err -> assertFailure (show err)
    Right (declEnv, holes, _, _, _) ->
      (length declEnv + length holes > 0) @? "Should produce something"
