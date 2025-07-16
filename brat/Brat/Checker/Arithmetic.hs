module Brat.Checker.Arithmetic where

import Brat.Syntax.Value (NumSum(..), Monotone(..))

nsConst :: Integer -> NumSum var
nsConst n = NumSum n []

nsVar :: var -> NumSum var
nsVar v = NumSum 0 [(Linear v, 1)]

nsMul :: NumSum var -> Integer -> NumSum var
nsMul _ 0 = NumSum 0 []
nsMul (NumSum n xs) m = NumSum (n*m) [(x, k*m) | (x, k) <- xs]

(-/) :: Integer -> Integer -> Integer
a -/ b = case a-b of
    x | x >0 -> x
    _ -> 0

simplify :: Ord var => (NumSum var, NumSum var) -> (NumSum var, NumSum var)
simplify (NumSum n xs, NumSum m ys) = defactor (NumSum (n -/ m) xs', NumSum (m -/ n) ys')
 where
  Pullbacks xs' _ ys' = pullbacks xs ys

  defactor (NumSum n xs, NumSum m ys) = (NumSum (n `div` g) [(x, k `div` g) | (x, k) <- xs]
                                  ,NumSum (m `div` g) [(y, k `div` g) | (y, k) <- ys]
                                  )
   where
    g = foldr gcd 0 (n : m : map snd (xs ++ ys))

data Pullbacks m = Pullbacks {
    leftDiff :: m,
    common :: m,
    rightDiff :: m
  }

class (Eq m, Monoid m) => PullbackMonoid m where
  pullbacks :: m -> m -> Pullbacks m

min_with_diffs :: Integer -> Integer -> Pullbacks Integer
min_with_diffs x y = let m = min x y in Pullbacks (x - m) m (y - m) -- if x < y then (0, x, y-x) else (x-y, y, 0)

instance Ord thing => PullbackMonoid [(thing, Integer)] where
  pullbacks [] ys = Pullbacks [] [] ys
  pullbacks xs [] = Pullbacks xs [] []
  pullbacks xxs@((x, n):xs) yys@((y, m):ys) = case compare x y of
        LT -> let Pullbacks {..} = pullbacks xs yys in Pullbacks {leftDiff=(x,n):leftDiff, ..}
        EQ -> let Pullbacks px pc py = pullbacks xs ys
                  Pullbacks qx qc qy = min_with_diffs n m
                  cons_non0 (t,q) ts = if q==0 then ts else (t,q):ts
               in Pullbacks {
                    leftDiff = cons_non0 (x, qx) px,
                    common = cons_non0 (x, qc) pc,
                    rightDiff = cons_non0 (y, qy) py
               }
        GT -> let Pullbacks {..} = pullbacks xxs ys in Pullbacks {rightDiff = (y,m):rightDiff, ..}

instance Ord var => PullbackMonoid (NumSum var) where
    pullbacks (NumSum n xs) (NumSum m ys) =
        let Pullbacks x c y = min_with_diffs n m
            Pullbacks {..} = pullbacks xs ys
        in Pullbacks (NumSum x leftDiff) (NumSum c common) (NumSum y rightDiff)
