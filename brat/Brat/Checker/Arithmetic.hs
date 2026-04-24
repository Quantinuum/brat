module Brat.Checker.Arithmetic where

import Data.Maybe (fromMaybe)
import qualified Data.Set as S

import Brat.Syntax.Value

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

type Eqn var = (NumSum var, NumSum var)

simplify :: Ord var => Eqn var -> Eqn var
simplify (NumSum n xs, NumSum m ys) = minOnLeft $ defactor (NumSum (n -/ m) xs', NumSum (m -/ n) ys')
 where
  Pullbacks xs' _ ys' = pullbacks xs ys

  defactor (NumSum n xs, NumSum m ys) = (NumSum (n `div` g) [(x, k `div` g) | (x, k) <- xs]
                                  ,NumSum (m `div` g) [(y, k `div` g) | (y, k) <- ys]
                                  )
   where
    g = foldr gcd 0 (n : m : map snd (xs ++ ys))

  minOnLeft (s1@(NumSum _ []), s2@(NumSum _ (_:_))) = (s2, s1)
  minOnLeft (s1@(NumSum _ (x:_)), s2@(NumSum _ (y:_))) | y<x = (s2, s1)
  minOnLeft eqn = eqn

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

-- Might not be necessary to sort vars but it's easy enough
vars :: Ord var => Eqn var -> [Monotone var]
vars (NumSum _ xs, NumSum _ ys) = merge (map fst xs) (map fst ys)
 where
  merge [] ys = ys
  merge xs [] = xs
  merge xxs@(x:xs) yys@(y:ys) = if x<y then x:(merge xs yys) else y:(merge xxs ys)

eFlip :: Eqn var -> Eqn var
eFlip (s1, s2) = (s2, s1)

eAdd :: Ord var => Eqn var -> Eqn var -> Eqn var
eAdd (s1, s2) (s1', s2') = simplify (s1 <> s1', s2 <> s2')

eSub :: Ord var => Eqn var -> Eqn var -> Eqn var
eSub e1 e2 = e1 `eAdd` (eFlip e2)

eMul :: Eqn var -> Integer -> Eqn var
eMul (s1, s2) m | m >= 0 = (s1 `multNumSum` m, s2 `multNumSum` m)
eMul e m = eMul (eFlip e) (-m)

lweight :: Eq var => Eqn var -> Monotone var -> Maybe Integer
lweight (NumSum _ ts, _) v = lookup ts
 where
  lookup ((x,n):_) | x == v = Just n
  lookup (_:xs) = lookup xs
  lookup [] = Nothing

sweight :: Eq var => Eqn var -> Monotone var -> Integer
sweight e v = fromMaybe (fromMaybe 0 $ lweight (eFlip e) v) $ lweight e v

gauss_elim :: forall var. Ord var => [Eqn var] -> [Eqn var]
gauss_elim eqns = fst $ foldl elim ([], eqns) (S.toList $ S.fromList $ mconcat $ map vars eqns)
 where
  -- first element of pair are reduced: each Eqn is the only one mentioning its first variable
  -- in second element of pair, no Eqn mentions any variable that is first var of any reduced
  -- variable identifies what to reduce, i.e. 'elim' constructs an equation where that var is first
  elim :: ([Eqn var], [Eqn var]) -> Monotone var -> ([Eqn var], [Eqn var])
  elim (redns, eqns) v = (e1:(map rm_v redns), (map rm_v eqns))
   where
    (e1, w1) = foldl1 eqn_one ((redns ++ eqns) >>= v_on_left)
    v_on_left :: Eqn var -> [(Eqn var, Integer)]
    v_on_left e = case sweight e v of
        0 -> []
        w | w<0 -> [(eFlip e, -w)]
          | otherwise -> [(e, w)]

    -- make an equation containing exactly one 'v'
    -- both arguments, and result, are (equation, number of 'v's)
    --     where equation has 'v' on LHS, and number is strictly positive
    eqn_one :: (Eqn var, Integer) -> (Eqn var, Integer) -> (Eqn var, Integer)
    eqn_one (e, 1) _ = (e, 1)
    eqn_one e@(_, w) e2@(_, w2) | w2 > w = eqn_one e (e2 `vlsub` e)
                                | w2 == w = e -- gcd is >1, best we can do
                                | otherwise = eqn_one (e `vlsub` e2) e2
    vlsub :: (Eqn var, Integer) -> (Eqn var, Integer) -> (Eqn var, Integer)
    vlsub (e1, w1) (e2, w2) = let e = e1 `eSub` e2 -- puts min var on left...perhaps we shouldn't?
                              in (,w1-w2) $ case sweight e v of
                                              w | w<0 -> eFlip e
                                                | w>0 -> e

    -- remove 'v' from equation 'e', where 'e' might be any equation
    rm_v e = let w = sweight e v
                 gw = gcd w w1
              in if w==0 then e else (e `eMul` (w1 `div` gw)) `eSub` (e1 `eMul` (w `div` gw))
