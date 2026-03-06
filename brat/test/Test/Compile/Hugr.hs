module Test.Compile.Hugr where

import Brat.Compiler (compileFile, CompilingHoles(..))
import Test.Checking (expectedCheckingFails)
import Test.Parsing (expectedParsingFails)
import Test.Util (expectFailForPaths)

import qualified Data.ByteString as BS
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
  ["app"
  --,"adder" -- not even checking yet
  ,"dollar_kind"
  ,"portpulling"
  ,"eatsfull" -- Compiling hopes #96
  ,"map" -- Compiling hopes #96
  ,"infer_thunks" -- Weird: Mismatch between caller and callee signatures in map call
  ,"infer_thunks2" -- Weird: Mismatch between caller and callee signatures in map call
  --,"repeated_app" -- not checking yet, but will be missing coercions, https://github.com/quantinuum-dev/brat/issues/413
  ]
  )

-- examples that we expect not to compile.
-- Note this does not include those with remaining holes; these are automatically skipped.
nonCompilingExamples = expectedCheckingFails ++ expectedParsingFails ++
  map ((++ ".brat") . ("examples" </>))
  ["fzbz"
  ,"let"
  ,"patterns"
  ,"qft"
  ,"infer" -- problems with undoing pattern tests
  ,"infer2" -- problems with undoing pattern tests
  ,"fanout" -- Contains Selectors
  ,"vectorise" -- Generates MapFun nodes which aren't implemented yet
  ,"vector_solve" -- Generates "Pow" nodes which aren't implemented yet
  ,"batcher-merge-sort" -- Generates MapFun nodes which aren't implemented yet
  -- Victims of #13
  ,"arith"
  ,"klet"
  ,"magic-state-distillation" -- also makes selectors
  ]

-- This is https://github.com/Quantinuum/brat/issues/101
nonCompilingTests = ["test/compilation/closures.brat"]

compileToOutput :: FilePath -> TestTree
compileToOutput file = testCaseInfo (show file) $ compileFile [] file >>= \case
    Right hugr_bytes -> do
          let outputExt = if file `elem` invalidExamples then "json.invalid" else "json"
          let outFile = outputDir </> replaceExtension (takeFileName file) outputExt
          -- lots of fun with lazy and even strict bytestrings
          -- returning many bytes before evaluation has completed
          BS.writeFile outFile $! (BS.toStrict hugr_bytes)
          pure $ "Written to " ++ outFile ++ " pending validation\n"
    Left (CompilingHoles _) -> pure "Skipped as contains holes"

setupCompilationTests :: IO TestTree
setupCompilationTests = do
  tests <- findByExtension [".brat"] prefix
  examples <- findByExtension [".brat"] examplesPrefix
  createDirectoryIfMissing False outputDir
  let compileTests = expectFailForPaths nonCompilingTests compileToOutput tests
  let examplesTests = testGroup "examples" $ expectFailForPaths nonCompilingExamples compileToOutput examples

  pure $ testGroup "compilation" (examplesTests:compileTests)
