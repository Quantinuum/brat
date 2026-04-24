module Brat.Checker.SolveConstraints where

import Brat.Checker.Helpers (mineToSolve)
import Brat.Checker.Monad (Checking)
import Brat.Checker.SolveNumbers (unifyNum, demandAtLeast)
import Brat.Syntax.Value
import Hasochism (N(..))

type Eqn v = (NumSum v, NumSum v)

(-/) :: Integer -> Integer -> Integer
a -/ b = case a-b of
    x | x >0 -> x
    _ -> 0

div0 :: Integer -> Integer -> Integer
div0 0 _ = 0
div0 a b = a `div` b


simplify :: Ord v => Eqn v -> Eqn v
simplify (NumSum n xs, NumSum m ys) = cas
  (NumSum (n' `div0` g) (xs' `divs` g)
  ,NumSum (m' `div0` g) (ys' `divs` g)
  )
 where
  n' = n -/ m
  m' = m -/ n

  g = g' `gcd` n' `gcd` m'

  (g', xs', ys') = aux xs ys

  consNon0 (t,q) ts = if q==0 then ts else (t,q):ts

  aux :: Ord v => [(v, Integer)] -> [(v, Integer)] -> (Integer, [(v, Integer)], [(v, Integer)])
  aux [] ys = (foldr gcd 0 (snd <$> ys), [], ys)
  aux xs [] = (foldr gcd 0 (snd <$> xs), xs, [])
  aux xxs@((x, n):xs) yys@((y, m):ys) = case compare x y of
    LT -> let (g, xs', ys') = aux xs yys in (gcd g n, (x, n):xs', ys')
    EQ -> let (g, xs', ys') = aux xs ys
              n' = n -/ m
              m' = m -/ n
          in  (g `gcd` n' `gcd` m', consNon0 (x, n') xs', consNon0 (y, m') ys')
    GT -> let (g, xs', ys') = aux xxs ys in (gcd g m, xs', (y, m):ys')

  divs :: [(v, Integer)] -> Integer -> [(v, Integer)]
  divs xs g = fmap (fmap (`div0` g)) xs

  cas :: Ord v => Eqn v -> Eqn v
  cas (lhs,rhs)
   | lhs <= rhs = (lhs,rhs)
   | otherwise = (rhs, lhs)

fulbournConstraint :: Eqn (VVar Z) -> Checking ()
fulbournConstraint (lhs,rhs)
 | Just lhs <- numSumToNum lhs
 , Just rhs <- numSumToNum rhs = do
   mine <- mineToSolve
   unifyNum mine lhs rhs
fulbournConstraint (lhs, NumSum n _)
 | Just lnv <- numSumToNum lhs = demandAtLeast n lnv
fulbournConstraint (NumSum n _, rhs)
 | Just rnv <- numSumToNum rhs = demandAtLeast n rnv

fulbournConstraint _ = pure ()
