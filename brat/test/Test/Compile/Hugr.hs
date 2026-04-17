module Test.Compile.Hugr where

import Control.Monad (forM)
import Data.HugrGraph (to_json)
import Brat.Compiler (compileFile, CompilingHoles(..))

import qualified Data.Map as M
import qualified Data.ByteString as BS
import System.Directory (createDirectoryIfMissing)
import System.FilePath
import Test.Tasty
import Test.Tasty.HUnit

prefix = "test/compilation"
examplesPrefix = "examples"
outputDir = prefix </> "output"

compileToOutput :: String -> FilePath -> TestTree
compileToOutput name file = testCaseInfo name $ do
    createDirectoryIfMissing False outputDir
    compileFile [] file >>= \case
        Right hs -> mconcat <$> (forM (M.toList hs) $ \(boxName, (hugr, splices)) -> do
            -- ignore splices for now
            let outFile = outputDir </> replaceExtension (takeFileName file) ((show boxName) ++ ".json")
            -- lots of fun with lazy and even strict bytestrings
            -- returning many bytes before evaluation has completed
            BS.writeFile outFile $! (BS.toStrict $ to_json hugr)
            pure $ "Written to " ++ outFile ++ " pending validation\n")
        Left (CompilingHoles _) -> pure "Skipped as contains holes"
