module Util where

import qualified Data.Map as M

zipSameLength :: [a] -> [b] -> Maybe [(a,b)]
zipSameLength (x:xs) (y:ys) = ((x,y):) <$> zipSameLength xs ys
zipSameLength [] [] = Just []
zipSameLength _ _ = Nothing

lookupBy :: (a -> Bool) -> (a -> b) -> [a] -> Maybe b
lookupBy _ _ [] = Nothing
lookupBy p f (x:xs) | p x = Just (f x)
                    | otherwise = lookupBy p f xs

maybeToRight :: e -> Maybe a -> Either e a
maybeToRight e Nothing = Left e
maybeToRight _ (Just a) = Right a

duplicatesWith :: Eq b => (a -> b) -> [a] -> [a]
duplicatesWith f xs = let (_, dups, _) = aux ([], [], xs) in dups
 where
  aux (visited, dups, []) = (visited, dups, [])
  aux (visited, dups, x:xs) | f x `elem` visited = aux (visited, x:dups, xs)
                              | otherwise = aux (f x:visited, dups, xs)

duplicates :: Eq a => [a] -> [a]
duplicates = duplicatesWith id

-- An infinite list of strings for names:
-- a,b,c,...,a2,b2,c2,...,aN,bN,cN
names :: [String]
names = do
  number <- nums
  letter <- ['a'..'z']
  return (letter:show number)
 where
  nums :: [Int]
  nums = [1..]

-- Versions of `Control.Arrow`'s (***) where one arrow is functorial
(^**) :: Functor f => (a -> f b) -> (a' -> b') -> (a, a') -> f (b, b')
(f ^** g) (a, a') = (,g a') <$> f a

(**^) :: Functor f => (a -> b) -> (a' -> f b') -> (a, a') -> f (b, b')
(f **^ g) (a, a') = (f a,) <$> g a'

infixr 3 **^
infixr 3 ^**

log2 :: Integer -> Maybe Integer
log2 m | m > 1, (n, 0) <- m `divMod` 2 = (1+) <$> log2 n
log2 1 = pure 0
log2 _ = Nothing

mapLup :: (Show k, Ord k) => String -> M.Map k v -> k -> v
mapLup lbl m k = case M.lookup k m of
  Nothing -> error $ "mapLup fail: " ++ lbl ++ "\n  " ++ show k
  Just v -> v

expect :: String -> Maybe a -> a
expect msg Nothing = error msg
expect _ (Just a) = a
