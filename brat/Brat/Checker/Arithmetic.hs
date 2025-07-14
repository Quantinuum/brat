module Brat.Checker.Arithmetic where

import Data.List (minimumBy)
import Data.Ord (comparing)

-- number plus sum over a sequence of (variable/Full * number), ordered
-- All Integers positive, all multipliers strictly so
data Sum var = Sum Integer [(Monotone var, Integer )]

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
