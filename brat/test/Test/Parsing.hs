module Test.Parsing (getParsingTests, expectedParsingFails) where

import Brat.Load

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Silver
import Test.Util (expectFailForPaths)

testParse :: FilePath -> TestTree
testParse file = testCase (show file) $ do
  cts <- readFile file
  case parseFile file cts of
    Left err -> assertFailure (show err)
    Right _ -> return () -- OK

expectedParsingFails = []

parseXF = expectFailForPaths expectedParsingFails testParse

getParsingTests :: IO TestTree
getParsingTests = testGroup "parsing" . parseXF <$> findByExtension [".brat"] "examples"
