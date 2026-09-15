module Brat.Compiler (printAST
                     ,printDeclsHoles
                     ,writeDot
                     ,compileToGraph
                     ,CompilingHoles(..)
                     ) where

import Brat.Checker.Types (TypedHole)
import Brat.Dot (toDotString)
import Brat.Elaborator
import Brat.Error
import Brat.Load
import Brat.Naming (Namespace, root, split)

import Control.Monad (forM, when)
import Control.Monad.Except
import Data.List (intercalate)
import qualified Data.Map as M

printDeclsHoles :: [FilePath] -> String -> IO ()
printDeclsHoles libDirs file = do
  env <- runExceptT $ loadFilename root libDirs file
  (declEnv, holes, _, _, _) <- eitherIO env
  putStrLn "Decls:"
  forM (M.toList declEnv) $ \(name, (src_tys, _vdecl)) ->
    putStrLn $ show name ++ " :: " ++ intercalate ", " (map (show . snd) src_tys)
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
  (_, _, _, graph, cs) <- eitherIO env
  writeFile out (toDotString graph cs)
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
