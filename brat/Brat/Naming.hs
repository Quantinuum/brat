module Brat.Naming where

import Data.List (intercalate)
import Bwd

type Namespace = (
   Bwd (String, Int)  -- The hierarchy-level we are in
  ,Int  -- The next free unique id
  )

newtype Name = MkName [(String, Int)] deriving Eq

instance Ord Name where
  compare (MkName a) (MkName b) = aux a b
   where
    aux n m | n == m = EQ
    aux ((x, i):xs) ((y, j):ys)
     | x == y = compare i j <> compare xs ys
     | otherwise = compare x y
    aux [] _ = LT
    aux _ [] = GT

fresh :: String -> Namespace -> (Name, Namespace)
fresh str (lvl, i) = (MkName (lvl <>> [(str, i)]), (lvl, i + 1))

split :: String -> Namespace -> (Namespace, Namespace)
split str (lvl, i) = ((lvl :< (str, i), 0), (lvl, i + 1))

root :: Namespace
root = (B0, 0)

hasPrefix :: [String] -> Name -> Maybe Name
hasPrefix [] name = Just name
hasPrefix (x:xs) (MkName ((y, _):ys))
 | x == y = hasPrefix xs (MkName ys)
 | otherwise = Nothing

instance Show Name where
  show (MkName x) = intercalate "_"  $ fmap (\(str, n) ->
                                                case n of
                                                  0 -> str
                                                  _ -> str ++ "_" ++ show n) x


class Monad m => FreshMonad m where
  freshName :: String -> m Name
  (-!) :: String -> m a -> m a
  whoAmI :: m (Bwd (String, Int))
