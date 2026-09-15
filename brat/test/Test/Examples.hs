module Test.Examples (getExamplesTests) where

import Brat.Parser (parseExpr)
import Brat.Checker (check, checkWithGraph)
import Brat.Checker.Types (ChkConnectors)
import Brat.Compiler (compileToGraph)
import Brat.Elaborator (elaborateChkNoun)
import Brat.FC (WC(..))
import Brat.Load (parseFile, VMod)
import Brat.Machine (interpretGraph)
import Brat.Naming (Namespace)
import Brat.Syntax.Common (Mode(..), Dir(..), Kind(..))
import Brat.Syntax.Raw (runDesugar, Desugarable(..), Raw, RawEnv)
import Test.Checking (parseAndCheckNamed)

import Control.Exception (catch)
import qualified Data.ByteString as BS
import Data.Char (isAlphaNum)
import Data.Functor ((<&>))
import Data.Hugr (isHole)
import Data.HugrGraph as HG
import Data.List (isPrefixOf)
import qualified Data.Text.Lazy as T
import qualified Data.Map as M
import Data.Maybe (fromJust, isJust)
import System.Directory (createDirectoryIfMissing)
import System.FilePath
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Silver
import Test.Tasty.ExpectedFailure


--import Debug.Trace

outputDir :: FilePath
outputDir = "test" </> "examples"

execTestPrefix :: T.Text
execTestPrefix = T.pack "--!exec"

interpreterOutputPrefix :: String
interpreterOutputPrefix = "Finished "

data FunctionTestType = SaveHugr T.Text -- arguments
                      | Output T.Text -- output (TODO add arguments)
                      | XfailOutput T.Text -- output

funcTest :: (Namespace, VMod) -> String -> String -> FunctionTestType -> TestTree
funcTest nsmod path func_name testTy = case testTy of
  SaveHugr arg_expr -> testCaseInfo func_name $ do
        arg <- case parseExpr (T.unpack $ T.strip arg_expr) of
          Left err -> assertFailure ("Could not parse arguments: " ++ show err)
          Right val -> pure val
        (WC fc raw_arg_noun) :: WC (Raw Chk Noun) <- case elaborateChkNoun arg of
          Left err -> assertFailure ("Could not elaborate arguments: " ++ show err)
          Right val -> pure val
        let env :: RawEnv = undefined -- ALAN ??
        arg_noun <- case runDesugar env (desugar' raw_arg_noun) of
          Left err -> assertFailure ("Could not desugar arguments: " ++ show err)
          Right val -> pure (WC fc val)
        let (ns, (oldDeclEnv, oldHoles, oldStore, oldGraph, oldCaps)) = nsmod
        oldHoles @?= [] -- do we need to skip interpreting if there are holes?
        -- Should we split the namespace here?
        let conns :: ChkConnectors Brat Chk Noun = ((), undefined) -- need [Tgt, BinderTypeBrat] i.e. inports of call to func_name
        ((((), ()), ((), chk_unders)), (noHoles, newStore, newGraph, noCaps)) <- case checkWithGraph (M.map fst oldDeclEnv) oldStore ns oldGraph (check arg_noun conns) of
          Left err -> assertFailure ("Could not check arguments: " ++ show err)
          Right val -> pure val
        chk_unders @?= []
        (noCaps, noHoles) @?= (M.empty, []) -- i.e. in arguments
        let nsmod = (ns, (oldDeclEnv, oldHoles, newStore, newGraph, oldCaps))
        
        hugr <- case interpretGraph nsmod func_name of
              Left s -> assertFailure $ "Expected hugr, got " ++ T.unpack s
              Right hugr -> pure hugr
        getHoles hugr @?= []
        -- output the hugr for validation
        let outFile = outputDir </> dropExtension (takeFileName path) ++ "_" ++ func_name <.> "json"
        createDirectoryIfMissing False outputDir
        BS.writeFile outFile $! (BS.toStrict $ HG.to_json hugr)
        pure $ "Written hugr to " ++ outFile ++ " pending validation"
  XfailOutput out -> expectFail (funcTest nsmod path func_name (Output out))
  Output out -> let expectedOutput = interpreterOutputPrefix ++ T.unpack (T.strip out)
                in testCase func_name $ case interpretGraph nsmod func_name of
      Left t -> T.unpack t @?= expectedOutput
      Right _ -> assertFailure $ "Expected output: '" ++ expectedOutput ++ "' but got a hugr!"

compilePrefix = "test/compilation"
compileOutputDir = compilePrefix </> "output"

getExamplesTests :: IO TestTree
getExamplesTests =  do
  paths <- findByExtension [".brat"] "examples"
  testGroup "examples" <$> mapM (\path -> readFile path >>= mkTest path) paths
 where
  mkTest :: String -> String -> IO TestTree
  mkTest path cts =
    if isPrefixOf "--!xfail-parsing" cts then
      pure $ testGroup (show path) [expectFail parseTest]
    else if isPrefixOf "--!xfail-checking" cts then
      pure $ testGroup (show path) [parseTest, expectFail checkTest]
    else do
      maybe_mod <- catch (compileToGraph [] path <&> Just) (\(e :: IOError) -> pure Nothing)
      let interpreterTests = case maybe_mod of
            Nothing -> [testCaseInfo "execution" $ pure "SKIPPED as did not compile"]
            Just nsmod -> findInterpreterTests nsmod
      pure $ case interpreterTests of
        [] -> testGroup (show path) [checkTest]
        intTests -> sequentialTestGroup path AllSucceed
            (checkTest:[testGroup "execution" intTests])
   where
    parseTest = testCase "parsing" $ do
      case parseFile path cts of
        Left err -> assertFailure (show err)
        Right _ -> return () -- OK
    checkTest = parseAndCheckNamed "checking" [] path
    findInterpreterTests :: (Namespace, VMod) -> [TestTree]
    findInterpreterTests nsmod = T.breakOnAll execTestPrefix (T.pack cts) <&> \(_, start) ->
      let (testLine, newlineDefn) = T.breakOn (T.pack "\n") start
          -- this repeats/roughly duplicates the logic for "identifiers" in the parser
          func_name = T.unpack $ T.takeWhile (\c -> isAlphaNum c || c == '_' || c == '\'') (T.drop 1 newlineDefn)
          -- testLine begins with execTestPrefix, then either
          -- " " and the expected result
          -- "-xfail " and the (un-)expected result
          -- "-hugr\n" (checks no splices, outputs hugr for validation)
          restLine = fromJust $ T.stripPrefix execTestPrefix testLine
      in case restLine of
           _ | Just args <- T.stripPrefix (T.pack "-hugr") restLine ->
                  funcTest nsmod path func_name (SaveHugr args)
           _ | Just out <- T.stripPrefix (T.pack "-xfail ") restLine ->
                  funcTest nsmod path func_name (XfailOutput out)
             | Just out <- T.stripPrefix (T.pack " ") restLine ->
                  funcTest nsmod path func_name (Output out)
             | otherwise -> error $ "Invalid exec test line: " ++ T.unpack testLine

getHoles :: Ord a => HugrGraph a -> [a]
getHoles hg = [n | n <- getNodes hg, isJust (isHole $ getOp hg n)]
