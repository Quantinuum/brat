module Brat.Checker.Arithmetic where

import Data.Functor ((<&>))
import Data.List (minimumBy, sort, nub, partition)
import Data.Maybe (fromMaybe)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Ord (comparing)
import Data.Monoid
import Bwd
import Data.Kind (Type)
import Util (log2)
import Control.Monad (ap)
import Control.Arrow (Arrow (first, (***)))

-- number plus sum over a sequence of (variable/Full * number), ordered
-- All Integers positive, all multipliers strictly so
data LinearComb var = LinearComb Integer [(NumVal var, Integer)]
  deriving (Eq, Show)

sConst :: Integer -> LinearComb var
sConst n = LinearComb n []

sVar :: var -> LinearComb var
sVar v = LinearComb 0 [(nVar v, 1)]

sMul :: LinearComb var -> Integer -> LinearComb var
sMul _ 0 = LinearComb 0 []
sMul (LinearComb n xs) m = LinearComb (n*m) [(x, k*m) | (x, k) <- xs]

lcSubst :: (a -> NumVal b) -> LinearComb a -> LinearComb b
lcSubst s (LinearComb c terms) = LinearComb c (first (>>= s) <$> terms) 

(-/) :: Integer -> Integer -> Integer
a -/ b = case a-b of
    x | x >0 -> x
    _ -> 0

-- A single `m1*a1 + ... + mn*an := c` constraint.
--
-- Invariants:
-- * no duplicate `m`s
-- * no zero `a`s
-- * `a1` is positive if it exists
-- * `m`s are in order
data Eqn' var x = [(Monotone var, x)] := x deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

type Eqn var = Eqn' var Integer

-- Ensures that invariants hold
normalise :: forall var. Ord var => Eqn var -> Eqn var
normalise (mas := c) = positive $ factor $ collect mas := c
 where
  -- Sort and add up terms with the same `m` and remove zeros
  collect :: Ord a => [(a, Integer)] -> [(a, Integer)]
  collect mas = foldr go [] (sort mas)
   where
     go (m, a) ((m', b):mas') | m == m' = (m', a+b) `no0` mas'
     go ma mas' = ma `no0` mas'

     no0 (_, 0) mas' = mas'
     no0 ma mas' = ma:mas'
  
  -- Eliminate any common factors
  factor :: Eqn var -> Eqn var
  factor eqn@(mas := c) = case foldr gcd c (snd <$> mas) of
    0 -> eqn
    g -> [(m, a `div` g) | (m, a) <- mas] := (c `div` g)
  
  -- Ensure that the first coefficient is positive
  positive :: Eqn var -> Eqn var
  positive eqn@(((_, a):_) := _) | a < 0 = fmap negate eqn
  positive eqn = eqn


instance Ord var => Monoid (Eqn var) where
  mempty = [] := 0
  mappend (mas := c) (mas' := c') = normalise ((mas ++ mas') := (c + c'))

instance Ord var => Semigroup (Eqn var) where
  (<>) = mappend


eqnFromLinearCombs :: Ord var => LinearComb var -> LinearComb var -> Eqn var
eqnFromLinearCombs (LinearComb c1 terms1) (LinearComb c2 terms2) = 
  mas1 := (c2 + u2) <> fmap negate (mas2 := (c1 + u1))
 where
  -- NumVal to upshift and either the empty list or a singleton list with a term
  term :: (NumVal var, Integer) -> (Integer, [(Monotone var, Integer)])
  term (NumValue up grow, coeff) = (up,) $ case grow of
      Constant0 -> []
      (StrictMonoFun (StrictMono numDoub mono)) -> [(mono, coeff * 2 ^ numDoub)]
  
  umas1 = term <$> terms1
  u1 = sum (fst <$> umas1)
  mas1 = concatMap snd umas1

  umas2 = term <$> terms2
  u2 = sum (fst <$> umas2)
  mas2 = concatMap snd umas2


eqnToLinearCombs :: Eqn var -> (LinearComb var, LinearComb var)
eqnToLinearCombs (mas := c) = (LinearComb posC (first numValue <$> posCoeffs), LinearComb negC ((numValue *** negate) <$> negCoeffs))
 where
  (posCoeffs, negCoeffs) = partition ((> 0) . snd) mas
  posC = max c 0
  negC = max (negate c) 0


type Equationz var = Bwd (Eqn var)

eliminate :: Ord var => Eqn var -- New equation
                     -> Eqn var -- Old equation
                     -> Eqn var -- New equation simplified by old equation
eliminate new@(mbs := _) old@(((m, a):_) := _) | Just b <- lookup m mbs =
    fmap (* a) new <> fmap (* negate b) old  -- Semigroup operation does the simplification
eliminate new _ = new

eliminatez :: Ord var => Eqn var -- New equation
                      -> Equationz var -- Old equations
                      -> Eqn var -- New equation simplified by old equations
eliminatez = foldl eliminate


data EqnClassification var 
  = Obviously Bool  -- Eqn is obviously true or false
  | Equivalently (NumVal var) (NumVal var)  -- Equivalent to a unification problem
  | Nullifying [var]  -- True iff a bunch of vars are all zero
  | EnsuringAtLeast (Monotone var) Integer  -- False unless expression is >= constant
  | EnsuringEven (Monotone var)  -- False unless expression is even
  | Difficult  -- Don't know what to do yet
  deriving Show

classifyEqn :: Eq var => Eqn var -> EqnClassification var
classifyEqn ([] := c) = Obviously (c == 0)
classifyEqn (mas := c) | all (even . snd) mas, odd c = Obviously False
classifyEqn (mas := c) | all ((> 0) . snd) mas, c < 0 = Obviously False
classifyEqn ([(m, a)] := c) | a == 1, c >= 0 = Equivalently (numValue m) (nConstant c)
                            | otherwise = Obviously False  -- m would need to be a fraction or negative
classifyEqn ([(m1, a1), (m2, a2)] := c) | Just e1 <- log2 a1, Just e2 <- log2 (negate a2) =
  Equivalently 
    (nPlus (max 0 (negate c)) (n2PowTimes e1 (numValue m1)))
    (nPlus (max 0 c) (n2PowTimes e2 (numValue m2)))
-- LinearComb of positive coefficients is zero iff all variables are zero
classifyEqn (mas := 0) | all ((> 0) . snd) mas = Nullifying $ nub (foldMap (foldMap pure . fst) mas)
-- If there is only one coefficient whose sign matches c, then that term must be a successor
classifyEqn eqn@(_ := c) 
  | c /= 0
  , mas := c <- fmap (* signum c) eqn  -- Normalise c to be positive
  , [(m, a)] <- filter ((> 0) . snd) mas  -- Check only one coefficient is positive
  = EnsuringAtLeast m ((c + a - 1) `div` a)  -- Then, `m` needs to be >= ceil(c / a)
classifyEqn (mas := c)
  | even c  -- An even constant
  , [(m, _)] <- filter (odd . snd) mas  -- with only one odd coefficient
  = EnsuringEven m  -- then the rest of the terms are even, and m must be too
classifyEqn _ = Difficult


substEqz :: Ord b => Equationz a -> (a -> NumVal b) -> (Equationz b, Bwd (EqnClassification b))
substEqz B0 _ = (B0, B0)
substEqz (eqnz :< eqn) s = case substEqz eqnz s of
  (eqnz', clz) -> let (left, right) = eqnToLinearCombs eqn in 
                  let eqn' = eqnFromLinearCombs (lcSubst s left) (lcSubst s right) in
                  let eqn'' = eliminatez eqn' eqnz' in
                  (eqnz' :< eqn'', clz :< classifyEqn eqn'')

-- simplify :: Ord var => Eqn var -> Eqn var
-- simplify (LinearComb n xs, LinearComb m ys) = minOnLeft $ defactor (LinearComb (n -/ m) xs', LinearComb (m -/ n) ys')
--  where
--   Pullbacks xs' _ ys' = pullbacks xs ys

--   defactor (LinearComb n xs, LinearComb m ys) = (LinearComb (n `div` g) [(x, k `div` g) | (x, k) <- xs]
--                                   ,LinearComb (m `div` g) [(y, k `div` g) | (y, k) <- ys]
--                                   )
--    where
--     g = foldr gcd 0 (n : m : map snd (xs ++ ys))

--   minOnLeft (s1@(LinearComb _ []), s2@(LinearComb _ (_:_))) = (s2, s1)
--   minOnLeft (s1@(LinearComb _ (x:_)), s2@(LinearComb _ (y:_))) | y<x = (s2, s1)
--   minOnLeft eqn = eqn

-- data Pullbacks m = Pullbacks {
--     leftDiff :: m,
--     common :: m,
--     rightDiff :: m
--   }

-- class (Eq m, Monoid m) => PullbackMonoid m where
--   pullbacks :: m -> m -> Pullbacks m

-- min_with_diffs :: Integer -> Integer -> Pullbacks Integer
-- min_with_diffs x y = let m = min x y in Pullbacks (x - m) m (y - m) -- if x < y then (0, x, y-x) else (x-y, y, 0)

-- instance Ord thing => PullbackMonoid [(thing, Integer)] where
--   pullbacks [] ys = Pullbacks [] [] ys
--   pullbacks xs [] = Pullbacks xs [] []
--   pullbacks xxs@((x, n):xs) yys@((y, m):ys) = case compare x y of
--         LT -> let Pullbacks {..} = pullbacks xs yys in Pullbacks {leftDiff=(x,n):leftDiff, ..}
--         EQ -> let Pullbacks px pc py = pullbacks xs ys
--                   Pullbacks qx qc qy = min_with_diffs n m
--                   cons_non0 (t,q) ts = if q==0 then ts else (t,q):ts
--                in Pullbacks {
--                     leftDiff = cons_non0 (x, qx) px,
--                     common = cons_non0 (x, qc) pc,
--                     rightDiff = cons_non0 (y, qy) py
--                }
--         GT -> let Pullbacks {..} = pullbacks xxs ys in Pullbacks {rightDiff = (y,m):rightDiff, ..}

-- instance Ord var => PullbackMonoid (LinearComb var) where
--     pullbacks (LinearComb n xs) (LinearComb m ys) =
--         let Pullbacks x c y = min_with_diffs n m
--             Pullbacks {..} = pullbacks xs ys
--         in Pullbacks (LinearComb x leftDiff) (LinearComb c common) (LinearComb y rightDiff)

-- -- Might not be necessary to sort vars but it's easy enough
-- vars :: Ord var => Eqn var -> [Monotone var]
-- vars (LinearComb _ xs, LinearComb _ ys) = merge (map fst xs) (map fst ys)
--  where
--   merge [] ys = ys
--   merge xs [] = xs
--   merge xxs@(x:xs) yys@(y:ys) = if x<y then x:(merge xs yys) else y:(merge xxs ys)

-- eFlip :: Eqn var -> Eqn var
-- eFlip (s1, s2) = (s2, s1)

-- eAdd :: Ord var => Eqn var -> Eqn var -> Eqn var
-- eAdd (s1, s2) (s1', s2') = simplify (s1 <> s1', s2 <> s2')

-- eSub :: Ord var => Eqn var -> Eqn var -> Eqn var
-- eSub e1 e2 = e1 `eAdd` (eFlip e2)

-- eMul :: Eqn var -> Integer -> Eqn var
-- eMul (s1, s2) m | m >= 0 = (s1 `sMul` m, s2 `sMul` m)
-- eMul e m = eMul (eFlip e) (-m)

-- lweight :: Eq var => Eqn var -> Monotone var -> Maybe Integer
-- lweight (LinearComb _ ts, _) v = lookup ts
--  where
--   lookup ((x,n):_) | x == v = Just n
--   lookup (_:xs) = lookup xs
--   lookup [] = Nothing

-- sweight :: Eq var => Eqn var -> Monotone var -> Integer
-- sweight e v = fromMaybe (fromMaybe 0 $ lweight (eFlip e) v) $ lweight e v

-- gauss_elim :: forall var. Ord var => [Eqn var] -> [Eqn var]
-- gauss_elim eqns = fst $ foldl elim ([], eqns) (S.toList $ S.fromList $ mconcat $ map vars eqns)
--  where
--   -- first element of pair are reduced: each Eqn is the only one mentioning its first variable
--   -- in second element of pair, no Eqn mentions any variable that is first var of any reduced
--   -- variable identifies what to reduce, i.e. 'elim' constructs an equation where that var is first
--   elim :: ([Eqn var], [Eqn var]) -> Monotone var -> ([Eqn var], [Eqn var])
--   elim (redns, eqns) v = (e1:(map rm_v redns), (map rm_v eqns))
--    where
--     (e1, w1) = foldl1 eqn_one ((redns ++ eqns) >>= v_on_left)
--     v_on_left :: Eqn var -> [(Eqn var, Integer)]
--     v_on_left e = case sweight e v of
--         0 -> []
--         w | w<0 -> [(eFlip e, -w)]
--           | otherwise -> [(e, w)]

--     -- make an equation containing exactly one 'v'
--     -- both arguments, and result, are (equation, number of 'v's)
--     --     where equation has 'v' on LHS, and number is strictly positive
--     eqn_one :: (Eqn var, Integer) -> (Eqn var, Integer) -> (Eqn var, Integer)
--     eqn_one (e, 1) _ = (e, 1)
--     eqn_one e@(_, w) e2@(_, w2) | w2 > w = eqn_one e (e2 `vlsub` e)
--                                 | w2 == w = e -- gcd is >1, best we can do
--                                 | otherwise = eqn_one (e `vlsub` e2) e2
--     vlsub :: (Eqn var, Integer) -> (Eqn var, Integer) -> (Eqn var, Integer)
--     vlsub (e1, w1) (e2, w2) = let e = e1 `eSub` e2 -- puts min var on left...perhaps we shouldn't?
--                               in (,w1-w2) $ case sweight e v of
--                                               w | w<0 -> eFlip e
--                                                 | w>0 -> e

--     -- remove 'v' from equation 'e', where 'e' might be any equation
--     rm_v e = let w = sweight e v
--                  gw = gcd w w1
--               in if w==0 then e else (e `eMul` (w1 `div` gw)) `eSub` (e1 `eMul` (w `div` gw))

-------------------------------- Number Values ---------------------------------
-- x is the TYPE of variables, e.g. SVar or (VVar n)
data NumVal x = NumValue
  { upshift :: Integer
  , grower  :: Fun00 x
  } deriving (Eq, Foldable, Functor, Traversable)

-- THIS IS NEW!!
instance Monad NumVal where
  return = pure
  NumValue u g >>= k = nPlus u (grow g)
   where
    grow Constant0 = nConstant 0
    grow (StrictMonoFun sm) = strictMono sm

    strictMono (StrictMono p m) = n2PowTimes p (mono m)

    mono (Linear x) = k x
    mono (Full sm) = nFull (strictMono sm)

instance Applicative NumVal where
  pure = nVar
  (<*>) = ap

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
