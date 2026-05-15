module Test.Examples (getExamplesTests) where

import Test.Checking (parseAndCheckNamed)
import Test.Compile.Hugr (compileToOutput, getHoles)
import Test.Config (IgnoreValidation(..))
import Brat.Load (parseFile)
import Brat.Machine (runInterpreter)
import Data.HugrGraph (to_json)

import qualified Data.ByteString as BS
import Data.ByteString.Lazy (ByteString)
import Data.Char (isAlphaNum)
import Data.Functor ((<&>))
import Data.List (isPrefixOf)
import Data.Maybe (fromJust)
import Data.Proxy
import qualified Data.Text.Lazy as T
import System.Console.ANSI (Color(..), ColorIntensity(..), ConsoleLayer(..), SGR(..), setSGRCode)
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode(..))
import System.FilePath
import System.Process (readCreateProcessWithExitCode, shell)
import Test.Tasty
import Test.Tasty.Providers
import Test.Tasty.Providers.ConsoleFormat (noResultDetails)
import Test.Tasty.HUnit
import Test.Tasty.Options (lookupOption, OptionDescription(..))
import Test.Tasty.Runners (FailureReason(..), Outcome(..), Result(..))
import Test.Tasty.Silver
import Test.Tasty.ExpectedFailure

--import Debug.Trace

data ValidationTest = VTest (IO ByteString) FilePath

instance IsTest ValidationTest where
  run opts (VTest hugr outFile) _ = do
    hugr_bytes <- hugr
    createDirectoryIfMissing True (takeDirectory outFile)
    BS.writeFile outFile $! (BS.toStrict $ hugr_bytes)
    (exitCode, stdout, stderr) <- readCreateProcessWithExitCode (shell $ "cat " ++ outFile ++ " | hugr_validator") ""
    let (outcome, msg1, msg2) = case exitCode of
          ExitSuccess -> (Success, "Validated hugr", "PASSED")
          _ -> case lookupOption @IgnoreValidation opts of
            IgnoreValidation False -> (Failure TestDepFailed, stderr, "FAILED")
            -- should we include the error message in the output for the skipped case? It might be a useful diagnostic, or just noise.
            IgnoreValidation True  -> (Success, "Validation failed", yellowText "SKIPPED")
    pure $ Result outcome msg1 msg2 0.0 noResultDetails
   where
    yellowText text = setSGRCode [SetColor Foreground Vivid Yellow] ++ text ++ setSGRCode [Reset]
  testOptions = pure [Option (Proxy :: Proxy IgnoreValidation)]

outputDir :: FilePath
outputDir = "test" </> "examples"

execTestPrefix :: T.Text
execTestPrefix = T.pack "--!exec"

interpreterOutputPrefix :: String
interpreterOutputPrefix = "Finished "

getExamplesTests :: IO TestTree
getExamplesTests =  do
  interpreterInPath <- checkValidatorInPath
  paths <- findByExtension [".brat"] "examples"
  testGroup "examples" <$> mapM (mkTest interpreterInPath) paths
 where
  mkTest :: Bool -> FilePath -> IO TestTree
  mkTest interpreterInPath path = readFile path <&> \cts ->
    let parseTest = testCase "parsing" $ do
          case parseFile path cts of
            Left err -> assertFailure (show err)
            Right _ -> return () -- OK
        checkTest = parseAndCheckNamed "checking" [] path
    in if isPrefixOf "--!xfail-parsing" cts then
         testGroup (show path) [expectFail parseTest]
       else if isPrefixOf "--!xfail-checking" cts then
         testGroup (show path) [parseTest, expectFail checkTest]
       else
        let execStrings = snd <$> T.breakOnAll execTestPrefix (T.pack cts)
            interpreterTests = concat $ interpreterTestsForExample interpreterInPath path <$> execStrings
            compileTest = compileToOutput "compilation" path
            checkAndCompile = if isPrefixOf "--!xfail-compilation" cts
              then [checkTest, expectFail compileTest] else [compileTest]
        in case interpreterTests of
          [] -> testGroup (show path) checkAndCompile
          intTests -> sequentialTestGroup path AllSucceed
              (checkAndCompile ++ [testGroup "execution" intTests])


interpreterTestsForExample :: Bool -> FilePath -> T.Text -> [TestTree]
interpreterTestsForExample interpreterInPath path start =
  let (testLine, newlineDefn) = T.breakOn (T.pack "\n") start
      -- this repeats/roughly duplicates the logic for "identifiers" in the parser
      func_name = T.unpack $ T.takeWhile (\c -> isAlphaNum c || c == '_' || c == '\'') (T.drop 1 newlineDefn)
      -- testLine begins with execTestPrefix, then either
      -- " " and the expected result
      -- "-xfail " and the (un-)expected result
      -- "-hugr\n" (checks no splices, outputs hugr for validation)
      restLine = fromJust $ T.stripPrefix execTestPrefix testLine
  in if (T.pack "-hugr") == restLine
     then let outFile = outputDir </> dropExtension (takeFileName path) ++ "_" ++ func_name <.> "json"
              makeHugr = do
                -- this completely recompiles the file for each test, which is pretty bad
                hugr <- runInterpreter [] path func_name >>= \case
                  Left s -> assertFailure $ "Expected hugr, got " ++ T.unpack s
                  Right hugr -> pure hugr
                getHoles hugr @?= []
                pure $ to_json hugr
          in [singleTest func_name (VTest makeHugr outFile)]
     else let (is_xfail, eOut) = case T.stripPrefix (T.pack "-xfail ") restLine of
                Just out -> (True, out)
                Nothing | Just out <- T.stripPrefix (T.pack " ") restLine -> (False, out)
                        | otherwise -> error $ "Invalid exec test line: " ++ T.unpack testLine
              expectedOutput = interpreterOutputPrefix ++ T.unpack (T.strip eOut)
          in (:[]) . (if is_xfail then expectFail else id) . testCase func_name $ do
            -- this completely recompiles the file for each test, which is pretty bad
            runInterpreter [] path func_name >>= \case
              Left t -> T.unpack t @?= expectedOutput
              Right _ -> assertFailure $ "Expected output: '" ++ expectedOutput ++ "' but got a hugr!"

checkValidatorInPath :: IO Bool
checkValidatorInPath = do
  (exitCode, output, _) <- readCreateProcessWithExitCode (shell "hugr_validator --version") ""
  if exitCode == ExitSuccess
  then pure ("hugr_validator 0." `isPrefixOf` output)
  else pure False

validateTest :: FilePath -> Assertion
validateTest file = do
  (exitCode, stdout, stderr) <- readCreateProcessWithExitCode (shell $ "cat " ++ file ++ " | hugr_validator") "" -- TODO: Put hugr output there
  case exitCode of
    ExitSuccess -> pure () --  "Validated hugr" -- TODO: Can we give a msg?
    _ -> assertFailure stderr
