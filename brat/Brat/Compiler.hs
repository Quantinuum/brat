module Brat.Compiler (printAST
                     ,printDeclsHoles
                     ,writeDot
                     ,compileFile
                     ,compileAndPrintFile
                     ,compileToGraph
                     ,CompilingHoles(..)
                     ) where

import Brat.Checker.Types (TypedHole, Modey(Kerny))
import Brat.Compile.Hugr
import Brat.Dot (toDotString)
import Brat.Elaborator
import Brat.Error
import Brat.Graph(Node(BratNode), NodeType(Box))
import Brat.Load
import Brat.Naming (Namespace, root, split, Name)
import Brat.Syntax.Port (OutPort)
import Brat.Syntax.Value (Val(VFun))


import Control.Exception (evaluate)
import Control.Monad (when)
import Control.Monad.Except
import qualified Data.ByteString.Lazy as BS
import Data.Foldable (for_)
import Data.HugrGraph (HugrGraph, NodeId, to_json)
import qualified Data.Map as M
import System.Exit (die)

printDeclsHoles :: [FilePath] -> String -> IO ()
printDeclsHoles libDirs file = do
  env <- runExceptT $ loadFilename root libDirs file
  (_, decls, holes, _, _, _) <- eitherIO env
  putStrLn "Decls:"
  print decls
  putStrLn ""
  putStrLn "Holes:"
  mapM_ print holes

-- Print an 80 column banner as the header and footer of some IO action's output
banner :: String -> IO a -> IO a
banner s m = putStrLn startText *> m <* putStrLn endText
 where
  startText = dashes ++ " " ++ s ++ space ++ dashes
  endText = replicate 80 '-'

  -- Add an extra space if `s` is odd to pad to 80 chars
  space = ' ' : replicate (len `mod` 2) ' '
  dashes = replicate (39 - hlen) '-'
  len = length s + 2
  hlen = len `div` 2

printAST :: Bool -> Bool -> String -> IO ()
printAST printRaw printAST file = do
  cts <- readFile file
  (_, env@(decls,_)) <- eitherIO $ parseFile file cts
  banner "Flat AST" $ mapM_ print decls
  env'@(decls, _, _) <- eitherIO $ addSrcContext file cts (elabEnv env)
  when printRaw $ banner "Raw AST" $ mapM_ print decls
  when printAST $
    banner "desugared AST" (mapM_ print =<< eitherIO (addSrcContext file cts (desugarEnv env')))

writeDot :: [FilePath] -> String -> String -> IO ()
writeDot libDirs file out = do
  env <- runExceptT $ loadFilename root libDirs file
  -- Discard captureSets; perhaps we could incorporate into the graph
  (_, _, _, _, graph, _) <- eitherIO env
  writeFile out (toDotString graph)
{-
 where
  isMain (PrefixName [] "main", _) = True
  isMain _ = False
-}

newtype CompilingHoles = CompilingHoles [TypedHole]

instance Show CompilingHoles where
  show (CompilingHoles hs) = unlines $
    "Can't compile file with remaining holes": fmap (("  " ++) . show) hs

compileToGraph :: [FilePath] -> String -> IO (Namespace, VMod)
compileToGraph libDirs file = do
  let (checkRoot, newRoot) = split "checking" root
  env <- runExceptT $ loadFilename checkRoot libDirs file
  (newRoot,) <$> eitherIO env

-- Map from box name to (compiled bytes, list of splices)
-- TODO: should keep Hugr as struct not ByteString
type CompilationResult = M.Map Name (HugrGraph, [(NodeId, OutPort)])

compileFile :: [FilePath] -> String -> IO (Either CompilingHoles CompilationResult)
compileFile libDirs file = do
  (newRoot, (_, _, holes, st, outerGraph, _)) <- compileToGraph libDirs file
  case holes of
    [] -> let boxes :: [Name] = [n | (n, BratNode (Box _ _) [] [(_, VFun Kerny _)]) <- (M.toList $ fst outerGraph)]
          in Right <$> (evaluate -- turns 'error' into IO 'die'
                    $ M.fromList [(n, compileKernel (newRoot, st, outerGraph) "root" n) | n <- boxes])
    hs -> pure $ Left (CompilingHoles hs)

compileAndPrintFile :: [FilePath] -> String -> IO ()
compileAndPrintFile libDirs file = compileFile libDirs file >>= \case
  Right hs -> for_ (M.toList hs) $ \(n, (hugr, splices)) -> do
    putStrLn $ "Compiled box: " ++ show n
    BS.putStr (to_json hugr)
    putStrLn $ "With splices: " ++ show splices
  Left err -> die (show err)
