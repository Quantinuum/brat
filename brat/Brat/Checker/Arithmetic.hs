module Brat.Checker.Arithmetic where

import Data.List (minimumBy)
import Data.Ord (comparing)

-- number plus sum over a sequence of (variable/Full * number), ordered
-- All Integers positive, all multipliers strictly so
data Sum var = Sum Integer [(Monotone var, Integer)]
  deriving (Eq, Show)

instance Ord var => Monoid (Sum var) where
    mempty = Sum 0 []
    mappend (Sum n ts) (Sum n' ts') = Sum (n + n') (merge ts ts')
     where
      merge [] ys = ys
      merge xs [] = xs
      merge xxs@((x, n):xs) yys@((y, m):ys) = case compare x y of
        LT -> (x, n):(merge xs yys)
        EQ -> (x, n+m):(merge xs ys)
        GT -> (y, m):(merge xxs ys)

instance Ord var => Semigroup (Sum var) where
    (<>) = mappend

sConst :: Integer -> Sum var
sConst n = Sum n []

sVar :: var -> Sum var
sVar v = Sum 0 [(Linear v, 1)]

sMul :: Sum var -> Integer -> Sum var
sMul _ 0 = Sum 0 []
sMul (Sum n xs) m = Sum (n*m) [(x, k*m) | (x, k) <- xs]

nv_to_sum :: NumVal var -> Sum var
nv_to_sum (NumValue up grow) = Sum up $ case grow of
    Constant0 -> []
    (StrictMonoFun (StrictMono numDoub mono)) -> [(mono, 2 ^ numDoub)]

nvs_to_sum :: Ord var => [NumVal var] -> Sum var
nvs_to_sum = foldMap nv_to_sum

(-/) :: Integer -> Integer -> Integer
a -/ b = case a-b of
    x | x >0 -> x
    _ -> 0

simplify :: Ord var => (Sum var, Sum var) -> (Sum var, Sum var)
simplify (Sum n xs, Sum m ys) = defactor (Sum (n -/ m) xs', Sum (m -/ n) ys')
 where
  Pullbacks xs' _ ys' = pullbacks xs ys

  defactor (Sum n xs, Sum m ys) = (Sum (n `div` g) [(x, k `div` g) | (x, k) <- xs]
                                  ,Sum (m `div` g) [(y, k `div` g) | (y, k) <- ys]
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

instance Ord var => PullbackMonoid (Sum var) where
    pullbacks (Sum n xs) (Sum m ys) =
        let Pullbacks x c y = min_with_diffs n m
            Pullbacks {..} = pullbacks xs ys
        in Pullbacks (Sum x leftDiff) (Sum c common) (Sum y rightDiff)


-------------------------------- Number Values ---------------------------------
-- x is the TYPE of variables, e.g. SVar or (VVar n)
data NumVal x = NumValue
  { upshift :: Integer
  , grower  :: Fun00 x
  } deriving (Eq, Foldable, Functor, Traversable)

instance Show x => Show (NumVal x) where
  show (NumValue 0 g) = show g
  show (NumValue n Constant0) = show n
  show (NumValue n g) = show n ++ " + " ++ show g

-- Functions which map 0 to 0
data Fun00 x
 = Constant0
 | StrictMonoFun (StrictMono x)
 deriving (Eq, Foldable, Functor, Traversable)

instance Show x => Show (Fun00 x) where
  show Constant0 = "0"
  show (StrictMonoFun sm) = show sm

-- Strictly increasing function
data StrictMono x = StrictMono
 { multBy2ToThe :: Integer
 , monotone :: Monotone x
 } deriving (Eq, Foldable, Functor, Ord, Traversable)

instance Show x => Show (StrictMono x) where
  show (StrictMono 0 m) = show m
  show (StrictMono n m) = let a = "2^" ++ show n
                              b = show (2 ^ n :: Int)
                          in minimumBy (comparing length) [b,a] ++ " * " ++ show m

data Monotone x
 = Linear x
 | Full (StrictMono x)
 deriving (Eq, Foldable, Functor, Ord, Traversable)

instance Show x => Show (Monotone x) where
  show (Linear v) = show v
  show (Full sm) = "(2^(" ++ show sm ++ ") - 1)"

{-
-- Reference semantics for NumValue types
class NumFun (t :: Type -> Type) where
  calculate :: t Integer -> Integer -- Variables already replaced by Integer
  numValue :: t x -> NumVal x

instance NumFun NumVal where
  calculate NumValue{..} = upshift + calculate grower
  numValue = id

instance NumFun Fun00 where
  calculate Constant0 = 0
  calculate (StrictMonoFun mono) = calculate mono

  numValue = NumValue 0

instance NumFun StrictMono where
  calculate StrictMono{..} = (2 ^ multBy2ToThe) * calculate monotone

  numValue = numValue . StrictMonoFun

instance NumFun Monotone where
  calculate (Linear n) = n
  calculate (Full sm) = full (calculate sm)
   where
    full n = (2 ^ n) - 1

  numValue = numValue . StrictMono 0
-}

nVar :: x -> NumVal x
nVar v = NumValue
  { upshift = 0
  , grower = StrictMonoFun
             (StrictMono
               { multBy2ToThe = 0
               , monotone = Linear v
               })
  }

nConstant :: Integer -> NumVal n
nConstant n = NumValue n Constant0

nZero :: NumVal n
nZero = nConstant 0

nPlus :: Integer -> NumVal n -> NumVal n
nPlus n (NumValue up g) = NumValue (up + n) g

n2PowTimes :: Integer -> NumVal n -> NumVal n
n2PowTimes n NumValue{..}
  = NumValue { upshift = upshift * (2 ^ n)
             , grower  = mult2PowGrower grower
             }
 where
  mult2PowGrower Constant0 = Constant0
  mult2PowGrower (StrictMonoFun sm)
   = StrictMonoFun (sm { multBy2ToThe = n + multBy2ToThe sm })

nFull :: NumVal n -> NumVal n
nFull NumValue{..} = case upshift of
  0 -> case grower of
    -- 2^0 - 1 = 0
    Constant0 -> NumValue 0 Constant0
    StrictMonoFun sm -> NumValue 0 (StrictMonoFun (StrictMono 0 (Full sm)))
  -- 2^(n + x) - 1  =  1 + 2 * (2^(n + x - 1) - 1)
  n -> nPlus 1 (n2PowTimes 1 (nFull (NumValue (n - 1) grower)))
