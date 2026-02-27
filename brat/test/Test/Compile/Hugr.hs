module Test.Compile.Hugr where

import Brat.Compiler (compileFile, CompilingHoles(..))
import Test.Checking (expectedCheckingFails)
import Test.Parsing (expectedParsingFails)
import Test.Util (expectFailForPaths)

import qualified Data.ByteString.Lazy as BS
import System.Directory (createDirectoryIfMissing)
import System.FilePath
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Silver

prefix = "test/compilation"
examplesPrefix = "examples"
outputDir = prefix </> "output"

-- examples that we expect to compile, but then to fail validation
invalidExamples :: [FilePath]
invalidExamples = (map ((++ ".brat") . ("examples" </>))
  ["adder"
  ,"repeated_app" -- missing coercions, https://github.com/quantinuum-dev/brat/issues/413
  ,"thunks"
  ])

-- examples that we expect not to compile.
-- Note this does not include those with remaining holes; these are automatically skipped.
nonCompilingExamples = expectedCheckingFails ++ expectedParsingFails ++
  map ((++ ".brat") . ("examples" </>))
    [
    ]

nonCompilingTests = []

compileToOutput :: FilePath -> TestTree
compileToOutput file = testCaseInfo (show file) $ compileFile [] file >>= \case
    Right bs -> do
      let outputExt = if file `elem` invalidExamples then "json.invalid" else "json"
      let outFile = outputDir </> replaceExtension (takeFileName file) outputExt
      BS.writeFile outFile bs
      pure $ "Written to " ++ outFile ++ " pending validation"
    Left (CompilingHoles _) -> pure "Skipped as contains holes"

setupCompilationTests :: IO TestTree
setupCompilationTests = do
  tests <- findByExtension [".brat"] prefix
  examples <- findByExtension [".brat"] examplesPrefix
  createDirectoryIfMissing False outputDir
  let compileTests = expectFailForPaths nonCompilingTests compileToOutput tests
  let examplesTests = testGroup "examples" $ expectFailForPaths nonCompilingExamples compileToOutput examples

  pure $ testGroup "compilation" (examplesTests:compileTests)
