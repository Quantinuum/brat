module Test.Checking (parseAndCheck, getCheckingTests, expectedCheckingFails) where

import Brat.Load
import Brat.Naming (root)

import Control.Monad.Except
import Data.List (isPrefixOf)
import Data.Functor ((<&>))
import qualified Data.Map as M
import System.FilePath
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Silver
import Test.Tasty.ExpectedFailure

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
  testGroup "examples" <$> mapM mkTest paths
 where
  mkTest :: FilePath -> IO TestTree
  mkTest path = readFile path <&> \cts ->
    if isPrefixOf "--!xfail-parsing" cts then
      expectFail $ testCase (show path) $ do
        case parseFile path cts of
          Left err -> assertFailure (show err)
          Right _ -> return () -- OK
    else if isPrefixOf "--!xfail-checking" cts then
      expectFail $ parseAndCheck [] path
    else parseAndCheck [] path

parseAndCheck :: [FilePath] -> FilePath -> TestTree
parseAndCheck libDirs file = testCase (show file) $ do
  env <- runExceptT $ loadFilename root libDirs file
  case env of
    Left err -> assertFailure (show err)
    Right (declEnv, holes, _, _, _) ->
      (length declEnv + length holes > 0) @? "Should produce something"
