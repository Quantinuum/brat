module Test.Checking (parseAndCheck, getCheckingTests, expectedCheckingFails) where

import Brat.Load
import Brat.Naming (root)

import Control.Monad.Except
import System.FilePath
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Silver
import Test.Tasty.ExpectedFailure
import qualified Data.Map as M

data XFailStatus = XFailParse | XFailCheck

expectedFails = M.fromList $
    (map ((, XFailCheck) . ("examples" </>)) ["nested-abstractors.brat"
                                             ,"karlheinz.brat"
                                             ,"karlheinz_alias.brat"
                                             ,"hea.brat"
                                             -- https://github.com/Quantinuum/brat/issues/92
                                             ,"repeated_app.brat"
                                             ,"adder.brat"
                                             ]) ++
    [("examples" </> "thin.brat", XFailParse)]

expectedCheckingFails :: [FilePath]
expectedCheckingFails = M.keys expectedFails

getCheckingTests :: IO TestTree
getCheckingTests =  do
  paths <- findByExtension [".brat"] "examples"
  let (tests, not_found) = foldr f ([], expectedFails) paths
  if M.null not_found
    then pure $ testGroup "examples" tests
    else error $ "Tried to XFAIL non-existent tests " ++ show (M.keys not_found)
 where
  f :: FilePath -> ([TestTree], M.Map FilePath XFailStatus) -> ([TestTree], M.Map FilePath XFailStatus)
  f path (ts, remaining_xfs) = let newTest = mkTest path (M.lookup path remaining_xfs)
                               in (newTest:ts, M.delete path remaining_xfs)

  mkTest :: FilePath -> Maybe XFailStatus -> TestTree
  mkTest path Nothing = parseAndCheck [] path
  mkTest path (Just XFailCheck) = expectFail $ mkTest path Nothing
  mkTest path (Just XFailParse) = expectFail $ testCase (show path) $ do
    cts <- readFile path
    case parseFile path cts of
      Left err -> assertFailure (show err)
      Right _ -> return () -- OK

parseAndCheck :: [FilePath] -> FilePath -> TestTree
parseAndCheck libDirs file = testCase (show file) $ do
  env <- runExceptT $ loadFilename root libDirs file
  case env of
    Left err -> assertFailure (show err)
    Right (declEnv, holes, _, _, _) ->
      (length declEnv + length holes > 0) @? "Should produce something"
