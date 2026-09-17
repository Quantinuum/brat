module Test.Examples (getExamplesTests) where

import Brat.Parser (parseExpr)
import Brat.Checker (checkWithGraph, check)
import Brat.Checker.Helpers (next, rowToRo)
import Brat.Checker.Monad (Checking)
import Brat.Checker.Types (Overs)
import Brat.Compiler (compileToGraph)
import Brat.Elaborator (elaborateChkNoun)
import Brat.Error (showError)
import Brat.FC (WC(..))
import Brat.Graph (NodeType(..))
import Brat.Load (VMod, checkDecl, parseFile)
import Brat.Machine (interpretGraph)
import Brat.Naming (Namespace)
import Brat.QualName (QualName, plain)
import Brat.Syntax.Common (Mode(..), Dir(..), Kind(..), Modey(..))
import Brat.Syntax.FuncDecl (FuncDecl(..), FunBody(..), Locality(..))
import Brat.Syntax.Port (End, Src)
import Brat.Syntax.Raw (runDesugar, Desugarable(..), Raw, RawEnv)
import Brat.Syntax.Value (AddR(..), BinderType, Ro(..), Stack(..), VarChanger(..), VDecl(..), stkLen, varChangerThroughRo)
import Brat.Syntax.Core (Term(..))
import Test.Checking (parseAndCheckNamed)

import Hasochism (N(..), Ny(..), Some(..), (:*)(..))

import Control.Exception (catch)
import Control.Monad (when)
import Data.Bifunctor (first)
import qualified Data.ByteString as BS
import Data.Char (isAlphaNum)
import Data.Functor ((<&>))
import Data.Hugr (isHole)
import Data.HugrGraph as HG
import qualified Data.Text.Lazy as T
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as L
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

make_test_func :: (Namespace, VMod) -> String -> T.Text -> Either String ((Namespace, VMod), String)
make_test_func nsmod func_name arg_expr = do
  arg <- first (\err -> "Could not parse arguments: " ++ show err) (parseExpr (T.unpack $ T.strip arg_expr))
  (WC fc raw_arg_noun) :: WC (Raw Chk Noun) <- first (("Could not elaborate arguments: " ++) . showError) (elaborateChkNoun arg)

  let env :: RawEnv = ([], [], M.empty) -- ALAN will this work? E.g. args referring to other funcs (higher-order)?
  arg_noun <- first (("Could not desugar arguments: " ++) . showError) (runDesugar env (desugar' raw_arg_noun))
  let app :: WC (Term Syn Noun) = WC fc $ (WC fc $ Force (WC fc (Var (plain func_name)))) :$: (WC fc arg_noun)
      (ns, (oldDeclEnv, oldHoles, oldStore, oldGraph, oldCaps)) = nsmod
      test_func_name = findNameNotIn (M.keysSet oldDeclEnv) ("test_" ++ func_name)
      doCheck :: Checking (VDecl, Overs Brat UVerb) = do
        -- Should we split the namespace here?

        -- We're gonna check a function application, i.e. `app` above, but we want
        -- to put that inside a VDecl, which requires declaring its types :(.
        (((), outs :: [(Src, BinderType Brat)]), ((), ())) <- let ?my = Braty in check app ((), ())
        
        -- TODO do we need a non-empty stack here?
        outs :: Some (Ro Brat Z :* Stack Z End) <- rowToRo Braty outs S0

        let decl = case outs of
              Some (ro :* _) ->  VDecl (FuncDecl test_func_name (Some ro) (NoLhs $ WC fc (Emb app)) fc Local)

        -- The decl needs wiring into an Id node whose *inputs* are the outs we just obtained,
        -- and whose *outputs* are another copy of that, hasochistically renumbered to come after.
        (unders, overs) <- case outs of
              Some (id_ins :* ends) -> case varChangerThroughRo (ParToInx (AddZ $ stkLen ends) ends) id_ins of
                Some (_ :* id_outs) -> do
                  (_, unders, overs, _) <- next test_func_name Id (S0, Some (Zy :* S0)) id_ins id_outs
                  pure (unders, overs)

        -- Finally check the decl onto that Id node.
        -- Of course this checks the application again!
        checkDecl [test_func_name] decl unders
        pure (decl, overs)

  ((decl, overs), (noHoles, newStore, newGraph, noCaps)) <- first (("Could not check arguments: " ++) . showError) $
       checkWithGraph (M.map fst oldDeclEnv) oldStore ns oldGraph doCheck
  -- sanity check the arguments
  when (noCaps /= M.empty) $ Left "arguments capture"
  when (length noHoles /= 0) $ Left "holes in arguments"

  let newDeclEnv = M.insert (plain test_func_name) (overs, decl) oldDeclEnv
      newNsmod = (ns, (newDeclEnv, oldHoles, newStore, newGraph, oldCaps))
  pure (newNsmod, test_func_name)

funcTest :: (Namespace, VMod) -> String -> String -> FunctionTestType -> TestTree
funcTest nsmod path func_name testTy = case testTy of
  SaveHugr arg_expr -> testCaseInfo func_name $ do
        (nsmod, test_func_name) <- if T.null arg_expr
            then pure (nsmod, func_name)
            else case make_test_func nsmod func_name arg_expr of
                  Left err -> assertFailure err
                  Right val -> pure val
        hugr <- case interpretGraph nsmod test_func_name of
              Left s -> assertFailure $ "Expected hugr, got " ++ T.unpack s
              Right hugr -> pure hugr
        (getHoles hugr == []) @? "holes in hugr"
        -- output the hugr for validation
        let outFile = outputDir </> dropExtension (takeFileName path) ++ "_" ++ test_func_name <.> "json"
        createDirectoryIfMissing False outputDir
        BS.writeFile outFile $! (BS.toStrict $ HG.to_json hugr)
        pure $ "Written hugr to " ++ outFile ++ " pending validation"
  XfailOutput out -> expectFail (funcTest nsmod path func_name (Output out))
  Output out -> let expectedOutput = interpreterOutputPrefix ++ T.unpack (T.strip out)
                in testCase func_name $ case interpretGraph nsmod func_name of
      Left t -> T.unpack t @?= expectedOutput
      Right _ -> assertFailure $ "Expected output: '" ++ expectedOutput ++ "' but got a hugr!"

findNameNotIn :: S.Set QualName -> String -> String
findNameNotIn ss cand | notMem cand = cand
                      | otherwise = fromJust $ L.find notMem (map (\n -> cand ++ "_" ++ show n) [0..])
  where
    notMem x = plain x `S.notMember` ss

compilePrefix = "test/compilation"
compileOutputDir = compilePrefix </> "output"

getExamplesTests :: IO TestTree
getExamplesTests =  do
  paths <- findByExtension [".brat"] "examples"
  testGroup "examples" <$> mapM (\path -> readFile path >>= mkTest path) paths
 where
  mkTest :: String -> String -> IO TestTree
  mkTest path cts =
    if L.isPrefixOf "--!xfail-parsing" cts then
      pure $ testGroup (show path) [expectFail parseTest]
    else if L.isPrefixOf "--!xfail-checking" cts then
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
