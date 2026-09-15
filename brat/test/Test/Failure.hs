module Test.Failure (getFailureTests) where

import Brat.Compiler (compileToGraph, CompilingHoles(..))

import Control.Exception
import Data.Text (pack)
import System.Exit (die, ExitCode(..))
import System.FilePath
import System.IO
import System.IO.Silently
import Test.Tasty
import Test.Tasty.Silver
import Test.Util (expectFailForPaths)


compileOrDie :: [FilePath] -> String -> IO ()
compileOrDie libDirs file = do
  (newRoot, (declEnv, holes, st, outerGraph, _)) <- compileToGraph libDirs file
  case holes of
    [] -> putStrLn "OK and no holes."
    hs -> die (show (CompilingHoles hs))

goldenTest file = goldenVsAction (takeBaseName file) (file <.> "golden") (runGetStderr file $ compileOrDie [] file) pack

getKernelTests :: IO TestTree
getKernelTests = testGroup "kernel" . fmap goldenTest <$> findByExtension [".brat"] "test/golden/kernel"

getCycleTests :: IO TestTree
getCycleTests = testGroup "cycle" . fmap goldenTest <$> findByExtension [".brat"] "test/golden/cycle"

getImportTests :: IO TestTree
getImportTests = testGroup "imports"
                 . fmap goldenTest
                 . filter ((`notElem` ignored) . takeBaseName)
                 <$> findByExtension [".brat"] "test/golden/imports"
 where ignored = ["lib"]

getBindingTests :: IO TestTree
getBindingTests = testGroup "binding" . fmap goldenTest <$> findByExtension [".brat"] "test/golden/binding"

getErrorTests :: IO TestTree
getErrorTests = testGroup "error" . expectFailForPaths ["test/golden/error/unreachablebranch.brat"] goldenTest <$> findByExtension [".brat"] "test/golden/error"

runGetStderr :: String -> IO () -> IO String
runGetStderr name action = do
    (output, ()) <- hCapture [stderr] $
      action `catch` \(ExitFailure c) -> return ()
    return output


getFailureTests = do
  bindingTests <- getBindingTests
  cycleTests   <- getCycleTests
  importTests  <- getImportTests
  kernelTests  <- getKernelTests
  errTests     <- getErrorTests
  pure $ testGroup "Failure" [bindingTests, cycleTests, importTests, kernelTests, errTests]
