module Test.Graph where

import Brat.Graph (Graph)
import Brat.Load (loadFiles)
import Brat.Naming (root)

import Control.Monad.Except (runExceptT)
import Data.List (sortOn)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Text (pack)
import System.FilePath ((<.>), takeBaseName)
import Test.Tasty
import Test.Tasty.HUnit (assertFailure)
import Test.Tasty.Silver

mkGraphTest :: FilePath -> IO TestTree
mkGraphTest bratFile = do
  contents <- readFile bratFile
  pure $ goldenVsAction (takeBaseName bratFile) (bratFile <.> "graph") (makeBratGraph contents) (pack . show)
 where
  makeBratGraph :: String -> IO Graph
  makeBratGraph contents = runExceptT (loadFiles root includeDirs bratFile contents) >>= \case
    -- ns is a map so will already be sorted
    Right (_, _, _, _, (ns, es), _) -> pure (ns, sortOn endNames es)
    Left err -> assertFailure (show err)

  endNames (inp, _, outp) = show inp ++ show outp

  -- Only look in cwd for files
  includeDirs = "." :| []

getGraphTests :: IO TestTree
getGraphTests = do
  tests <- findByExtension [".brat"] "test/golden/graph"
  testGroup "Graph Tests" <$> traverse mkGraphTest tests
