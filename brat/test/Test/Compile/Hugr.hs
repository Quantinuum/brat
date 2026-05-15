module Test.Compile.Hugr (compileToOutput, getHoles) where

import Control.Monad (forM)
import qualified Data.Map as M
import qualified Data.ByteString as BS
import System.Console.ANSI (Color(..), ColorIntensity(..), ConsoleLayer(..), SGR(..), setSGRCode)
import System.Directory (createDirectoryIfMissing)
import System.FilePath
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Providers (IsTest(..))
import Test.Tasty.Providers.ConsoleFormat (noResultDetails)
import Test.Tasty.Runners (FailureReason(..), Result(..), Outcome(..), TestTree(..))

import Data.Hugr (isHole)
import Data.HugrGraph (to_json, getOp, HugrGraph, getNodes)
import Data.List (sort)
import Data.Maybe (isJust)
import Brat.Compiler (compileFile, CompilingHoles(..))

data HugrTest = Validate TestTree | Skipped String | SkipNoValidator

instance IsTest HugrTest where
  -- BAD: Uses implementation
  run opts (Validate (SingleTest _ t)) f = run opts t f
  run opts (Skipped msg) f = pure $ Result (Failure TestDepFailed) msg (yellowText "SKIPPED") 0.0 noResultDetails
   where
    yellowText text = setSGRCode [SetColor Foreground Vivid Yellow] ++ text ++ setSGRCode [Reset]

  testOptions = pure []

prefix = "test/compilation"
outputDir = prefix </> "output"

compileToOutput :: String -> FilePath -> TestTree
compileToOutput name file = testCaseInfo name $ do
    createDirectoryIfMissing False outputDir
    compileFile [] file >>= \case
        Right hs -> mconcat <$> (forM (M.toList hs) $ \(boxName, (hugr, holes)) -> do
            sort (getHoles hugr) @?= sort holes
            -- ignore splices for now
            let outFile = outputDir </> replaceExtension (takeFileName file) ((show boxName) ++ ".json")
            -- lots of fun with lazy and even strict bytestrings
            -- returning many bytes before evaluation has completed
            BS.writeFile outFile $! (BS.toStrict $ to_json hugr)
            pure $ "Written to " ++ outFile ++ " pending validation\n")
        Left (CompilingHoles _) -> pure "Skipped as contains holes"

getHoles :: Ord a => HugrGraph a -> [a]
getHoles hg = [n | n <- getNodes hg, isJust (isHole $ getOp hg n)]
