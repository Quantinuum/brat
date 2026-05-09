module Test.Checking (parseAndCheck, parseAndCheckNamed) where

import Brat.Load
import Brat.Naming (root)

import Test.Tasty
import Test.Tasty.HUnit

parseAndCheck :: [FilePath] -> FilePath -> TestTree
parseAndCheck libDirs file = parseAndCheckNamed (show file) libDirs file

parseAndCheckNamed :: String -> [FilePath] -> FilePath -> TestTree
parseAndCheckNamed name libDirs file = testCase name $ do
  (env, maybeErr) <- loadFilename root libDirs file
  case maybeErr of
    Left err -> assertFailure (show err)
    Right () ->
      let (declEnv, holes, _, _, _) = env
      in (length declEnv + length holes > 0) @? "Should produce something"
