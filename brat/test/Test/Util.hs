module Test.Util where

import Brat.Checker
import Brat.Checker.Monad
import Brat.Checker.Types (initStore, emptyEnv)
import Brat.Error
import Brat.FC
import Brat.Naming

import qualified Data.Set as S
import Test.Tasty
import Test.Tasty.HUnit
import Data.List (isInfixOf)
import Test.Tasty.ExpectedFailure

runEmpty = run emptyEnv initStore root

assertChecking :: Checking a -> Assertion
assertChecking m = case runEmpty $ localFC (FC (Pos 0 0) (Pos 0 0)) m of
  Right _ -> pure ()
  Left err -> assertFailure (showError err)

assertCheckingFail :: Show a => String -> Checking a -> Assertion
assertCheckingFail needle m = case runEmpty $ localFC (FC (Pos 0 0) (Pos 0 0)) m of
  Right res -> assertFailure ("Computation produced result " ++ show res ++ " when should have Thrown")
  Left err -> let shown = showError err in
    if isInfixOf needle shown then pure () else assertFailure ("Unexpected error " ++ shown)

expectFailForPaths :: [FilePath] -> (FilePath -> TestTree) -> [FilePath] -> [TestTree]
expectFailForPaths xf makeTest paths = if S.null not_found then tests else
                                    error $ "Tried to XFAIL non-existent tests " ++ show not_found
 where
  f :: FilePath -> ([TestTree], S.Set FilePath) -> ([TestTree], S.Set FilePath)
  f path (ts, remaining_xfs) = let newTest = (if S.member path remaining_xfs then expectFail else id) $ makeTest path
                               in (newTest:ts, S.delete path remaining_xfs)
  (tests, not_found) = foldr f ([], S.fromList xf) paths
