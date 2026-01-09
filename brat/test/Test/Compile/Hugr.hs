module Test.Compile.Hugr where

import Control.Monad (forM)
import Data.HugrGraph (to_json)
import Brat.Compiler (compileFile, CompilingHoles(..))
import Test.Checking (expectedCheckingFails)
import Test.Parsing (expectedParsingFails)
import Test.Util (expectFailForPaths)

import qualified Data.ByteString.Lazy as BS
import qualified Data.Map as M
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
  ,"app"
  ,"dollar_kind"
  --,"portpulling" -- compiling just kernels is fine
  ,"eatsfull" -- Compiling hopes #96
  ,"map" -- Compiling hopes #96
  ,"infer_thunks" -- Weird: Mismatch between caller and callee signatures in map call
  ,"infer_thunks2" -- Weird: Mismatch between caller and callee signatures in map call
  ,"repeated_app" -- missing coercions, https://github.com/quantinuum-dev/brat/issues/413
  ,"thunks"]
  ) ++ ["test/compilation/closures.brat"] -- fails to compile but still spits out some JSON (not whole Hugr)

-- examples that we expect not to compile.
-- Note this does not include those with remaining holes; these are automatically skipped.
nonCompilingExamples = expectedCheckingFails ++ expectedParsingFails ++
  map ((++ ".brat") . ("examples" </>))
  [--"fzbz" -- can compile just kernels
  --,"ising" -- can compile just kernels
  --,"let" -- can compile just kernels
  --,"patterns" -- can compile just kernels
  --,"qft" -- can compile just kernels
  --,"infer" -- problems with undoing pattern tests -- can compile just kernels
  --,"infer2" -- problems with undoing pattern tests -- can compile just kernels
  "fanout" -- Contains Selectors
  --,"vectorise" -- Generates MapFun nodes which aren't implemented yet -- can compile just kernels
  --,"vector_solve" -- Generates "Pow" nodes which aren't implemented yet -- can compile just kernels
  --,"batcher-merge-sort" -- Generates MapFun nodes which aren't implemented yet -- can compile just kernels
  -- Victims of #13
  --,"arith" -- can compile just kernels
  ,"cqcconf"
  ,"imports"
  ,"klet"
  ,"magic-state-distillation" -- also makes selectors
  --,"rus" -- can compile just kernels
  ,"teleportation"
  --,"vlup_covering" -- can compile just kernels
  ]

compileToOutput :: FilePath -> TestTree
compileToOutput file = testCaseInfo (show file) $ compileFile [] file >>= \case
    Right hs ->
      let outputExt = if file `elem` invalidExamples then "json.invalid" else "json"
      in mconcat <$> (forM (M.toList hs) $ \(boxName, (hugr, splices)) -> do
        -- ignore splices for now
        let outFile = outputDir </> replaceExtension (takeFileName file) ((show boxName) ++ "." ++ outputExt)
        BS.writeFile outFile (to_json hugr)
        pure $ "Written to " ++ outFile ++ " pending validation\n")
    Left (CompilingHoles _) -> pure "Skipped as contains holes"

setupCompilationTests :: IO TestTree
setupCompilationTests = do
  tests <- findByExtension [".brat"] prefix
  examples <- findByExtension [".brat"] examplesPrefix
  createDirectoryIfMissing False outputDir
  let compileTests = compileToOutput <$> tests
  let examplesTests = testGroup "examples" $ expectFailForPaths nonCompilingExamples compileToOutput examples

  pure $ testGroup "compilation" (examplesTests:compileTests)
