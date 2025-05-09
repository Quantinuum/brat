{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}

module Brat.Syntax.Value {-(VDecl
                         ,VVar(..)
                         ,NumValue(..)
                         ,Fun00(..)
                         ,StrictMono(..), Monotone(..)
                         ,nZero, nVar, nConstant
                         ,nPlus, n2PowTimes, nFull
                         ,pattern TNat, pattern TInt
                         ,pattern TFloat, pattern TBool
                         ,pattern TText, pattern TOption
                         ,pattern TUnit, pattern TNil, pattern TCons
                         ,pattern TList, pattern TVec
                         ,Value(..)
                         ,BinderType
                         ,ValPat(..), valMatch, valMatches
                         ,NumPat(..), numMatch
                         ,DeBruijn(..), VarChanger(..), changeVars
                         ,doesItBind, doesItBind2
                         ,endVal, varVal
                         ,FunVal(..), value
                         )-} where

import Brat.Error
import Brat.QualName
import Brat.Syntax.CircuitProperties
import Brat.Syntax.Common hiding (pattern PNone)
import Brat.Syntax.Core (Term (..))
import Brat.Syntax.FuncDecl (FunBody, FuncDecl(..))
import Bwd
import Hasochism

import Data.List (intercalate, minimumBy)
import Data.Ord (comparing)
import Data.Kind (Type)
import Data.Maybe (isJust)
import Data.Type.Equality ((:~:)(..), testEquality)

newtype VDecl = VDecl (FuncDecl (Some (Ro Brat Z)) (FunBody Term Noun))

instance MODEY Brat => Show VDecl where
  show (VDecl decl) = show $ aux decl
   where
    aux :: FuncDecl (Some (Ro Brat Z)) body -> FuncDecl String body
    aux (FuncDecl { .. }) = case fnSig of
      Some sig -> FuncDecl { fnName = fnName, fnSig = show sig, fnBody = fnBody, fnLoc = fnLoc, fnLocality = fnLocality }

------------------------------------ Variable Indices ------------------------------------
-- Well scoped de Bruijn indices
data Inx :: N -> Type where
  -- We need `S n`, to say that there are >0 variables to choose the 0th from
  VZ :: Inx (S n)
  VS :: Inx n -> Inx (S n)

deriving instance Eq (Inx n)

instance Show (Inx n) where
  show = show . toNat
   where
    toNat :: forall n. Inx n -> Int
    toNat VZ = 0
    toNat (VS n) = 1 + toNat n

data AddR :: N -> N -> N -> Type where
  AddZ :: Ny out -> AddR out Z out
  AddS :: AddR out inn tot -> AddR out (S inn) (S tot)

-- If we have `out` outer variables on the left, then `inn` inner variables,
-- work out where a given `Inx` lies
outOrInn :: AddR out inn tot -> Inx tot -> Either (Inx out) (Inx inn)
-- There are no inner variables (because of AddZ), so everything lives in outer
outOrInn (AddZ _) inx = Left inx
-- There is at least 1 inner variable (because of AddS), so VZ is inner
outOrInn (AddS _) (VZ {- :: Inx (S tot) -}) = Right (VZ {- Inx (S inn) -})
outOrInn (AddS a) (VS inx) = case outOrInn a inx of
  -- inx is inner, put the VS back
  Right (inx {- :: Inx inn -}) -> Right (VS inx {- :: Inx (S inn) -})
  -- inx is outer, we don't care how many inner vars we passed to get to it
  Left (inx {- :: Inx out -}) -> Left (inx {- :: Inx out -})

injOut :: AddR out inn tot -> Inx out -> Inx tot
injOut (AddZ _) v = v
injOut (AddS a) v = VS $ injOut a v

injInn :: AddR out inn tot -> Inx inn -> Inx tot
injInn (AddZ _) v = impossible v
injInn (AddS _) VZ = VZ
injInn (AddS a) (VS v) = VS $ injInn a v

impossible :: Inx Z -> a
impossible v = case v of {}

------------------------------------ Stack ------------------------------------

findInx :: Eq x => Stack Z x n -> x -> Maybe (Inx n)
findInx S0 _ = Nothing
findInx (xz :<< x) x'
  | x == x' = Just VZ
  | otherwise = VS <$> findInx xz x'

data Stack :: N -> Type -> N -> Type where
  S0 :: Stack n x n
  (:<<) :: Stack n x m -> x -> Stack n x (S m)
infixl 7 :<<
deriving instance Show t => Show (Stack n t m)

traverseStack :: Monad m => (s -> m t) -> Stack i s j -> m (Stack i t j)
traverseStack _ S0 = pure S0
traverseStack f (zx :<< x) = (:<<) <$> traverseStack f zx <*> f x

-- Having a valid `Inx n` guarantees the Stack isn't empty
proj :: Stack Z x n -> Inx n -> x
proj S0 v = impossible v
proj (_ :<< x) VZ = x
proj (stk :<< _) (VS i) = proj stk i

(<<+) :: Stack l x n -> Stack n x m -> Stack l x m
S0 <<+ stk = stk
stk <<+ S0 = stk
stk <<+ (stk' :<< x) = stk <<+ stk' :<< x

stackLen :: Stack Z x n -> Ny n
stackLen S0 = Zy
stackLen (s :<< _) = Sy (stackLen s)

stkList :: Stack i a j -> [a]
stkList S0 = []
stkList (stk :<< a) = stkList stk ++ [a]

infixr 8 <<+

bwdStack :: Bwd x -> Some (Ny :* Stack Z x)
bwdStack B0 = Some (Zy :* S0)
bwdStack (zx :< x) = case bwdStack zx of
  Some (ny :* stk) -> Some (Sy ny :* (stk :<< x))

------------------------------------ Values ------------------------------------
-- Environment of closed values of size `top`
type Valz = Stack Z (Val Z)
type Semz = Stack Z Sem

data VVar :: N -> Type where
  VPar :: End -> VVar n  -- Has to be declared in the Store (for equality testing)
  VInx :: Inx n -> VVar n

deriving instance Show (VVar n)

instance Eq (VVar n) where
  (VPar e0) == (VPar e1) = e0 == e1
  (VInx i) == (VInx i') = i == i'
  _ == _ = False

-- More syntactic, called "Term" elsewhere in literature (not in BRAT)
-- Contains Inx's up to n-1, no Lvl's
data Val :: N -> Type where
  VNum :: NumVal (VVar n) -> Val n
  VCon :: QualName -> [Val n] -> Val n
  VLam :: Val (S n) -> Val n -- Just body (binds DeBruijn index n)
  VFun :: MODEY m => Modey m -> FunTy m n -> Val n
  VApp :: VVar n -> Bwd (Val n) -> Val n

-- Define a naive version of equality, which only says whether the data
-- structures are on-the-nose equal
instance Eq (Val n) where
  VNum a == VNum b = a == b
  (VCon c xs) == (VCon d ys) = c == d && xs == ys
  (VLam x) == (VLam y) = x == y
  (VFun m cty) == (VFun m' cty') = case testEquality m m' of
    Just Refl -> cty == cty'
    Nothing -> False
  (VApp v zx) == (VApp w zy) = v == w && zx == zy
  _ == _ =  False

instance MODEY m => Eq (FunTy m i) where
  (FunTy ps ss ts) == (FunTy qs us vs) = ((eqProps (modey @m) ps qs) &&) $ case roEq (modey @m) ss us of
                                   Just Refl -> isJust (roEq (modey @m) ts vs)
                                   Nothing -> False
   where
    roEq :: forall m i j k. Modey m -> Ro m i j -> Ro m i k -> Maybe (j :~: k)
    roEq _ R0 R0 = Just Refl
    roEq my (RPr x ro) (RPr y rp) | x == y = roEq my ro rp
    roEq Braty (REx x ro) (REx y rp) | x == y = case roEq Braty ro rp of
      Just Refl -> Just Refl
      Nothing -> Nothing
    roEq _ _ _ = Nothing

data SVar = SPar End | SLvl Int
 deriving (Show, Eq)

-- Semantic value, used internally by normalization; contains Lvl's but no Inx's
data Sem where
  SNum :: NumVal SVar -> Sem
  SCon :: QualName -> [Sem] -> Sem
  -- Second is just body, we do NOT substitute under the binder,
  -- instead we stash Sem's for each free DeBruijn index into the first member:
  SLam :: Stack Z Sem n -> Val (S n) -> Sem
  SFun :: MODEY m => Modey m -> Stack Z Sem n -> FunTy m n -> Sem
  SApp :: SVar -> Bwd Sem -> Sem
  -- Sum types, stash like SLam (shared between all variants)
  SSum :: MODEY m => Modey m -> Stack Z Sem n -> [Some (Ro m n)] -> Sem
deriving instance Show Sem

data FunTy :: Mode -> N -> Type where
  FunTy :: Properties m -> Ro m i j -> Ro m j k -> FunTy m i

pattern (:->>) :: Ro Brat i j -> Ro Brat j k -> FunTy Brat i
pattern ss :->> ts = FunTy () ss ts

instance MODEY m => Show (FunTy m n) where
  -- Properties don't exist in the surface syntax, so hide them from the user here.
  show (FunTy _ ri ro) = unwords [show ri, arrow, show ro]
   where
    arrow = case modey :: Modey m of
      Braty -> "->"
      Kerny -> "-o"

data Ro :: Mode
        -> N -- The number of free variables (in scope) at the start (bottom)
        -> N -- The number of free variables at the end (top)
        -> Type where
  R0 :: Ro m bot bot
  -- Existential quantification
  REx :: {---------} (PortName, TypeKind)
      -> {------------------------------} Ro Brat (S bot) top
      -> Ro Brat bot {----------------------------------} top
  -- Pairing
  RPr :: {------} (PortName, Val bot)
      -> {--------------------------} Ro m bot top
      -> Ro m bot {--------------------------} top


instance forall m top bot. MODEY m => Show (Ro m bot top) where
  show ro = intercalate ", " $ roToList ro
   where
    roToList :: forall bot. Ro m bot top -> [String]
    roToList R0 = []
    roToList (RPr (p, ty) ro) = let tyStr = case modey :: Modey m of
                                      Braty -> show ty
                                      Kerny -> show ty
                                in  ('(':p ++ " :: " ++ tyStr ++ ")"):roToList ro
    roToList  (REx (p, k) ro) = ('(':p ++ " :: " ++ show k ++ ")"):roToList ro

instance Show (Val n) where
  show v@(VCon _ _) | Just vs <- asList v = show vs
   where
    asList (VCon (PrefixName [] "nil") []) = Just []
    asList (VCon (PrefixName [] "cons") [hd, tl]) = (hd:) <$> asList tl
    asList _ = Nothing
  show (VCon c []) = show c
  show (VCon c vs) = show c ++ "(" ++ intercalate ", " (show <$> vs) ++ ")"
  show (VNum v) = show v
  show (VFun m cty) = "{ " ++ modily m (show cty) ++ " }"
  show (VApp v ctx) = "VApp " ++ show v ++ " " ++ show ctx
  show (VLam body) = "VLam " ++ show body

---------------------------------- Patterns -----------------------------------
pattern TNat, TInt, TFloat, TBool, TText, TUnit, TNil :: Val n
pattern TNat = VCon  (PrefixName [] "Nat") []
pattern TInt = VCon  (PrefixName [] "Int") []
pattern TFloat = VCon (PrefixName [] "Float") []
pattern TBool = VCon  (PrefixName [] "Bool") []
pattern TText = VCon (PrefixName [] "String") []
pattern TUnit = VCon (PrefixName [] "nil") []
pattern TNil = VCon (PrefixName [] "nil") []

pattern TList, TOption :: Val n -> Val n
pattern TList ty = VCon (PrefixName [] "List") [ty]
pattern TOption ty = VCon (PrefixName [] "Option") [ty]

pattern TVec, TCons :: Val n -> Val n -> Val n
pattern TVec ty n = VCon (PrefixName [] "Vec") [ty, n]
pattern TCons x ys = VCon (PrefixName [] "cons") [x, ys]

pattern TQ, TMoney, TBit :: Val n
pattern TQ = VCon (PrefixName [] "Qubit") []
pattern TMoney = VCon (PrefixName [] "Money") []
pattern TBit = VCon (PrefixName [] "Bit") []

type family BinderType (m :: Mode) where
  BinderType Brat = KindOr (Val Z)
  BinderType Kernel = Val Z

type family BinderVal (m :: Mode) where
  BinderVal Brat = Val Z
  BinderVal Kernel = KernelVal Z

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
 } deriving (Eq, Foldable, Functor, Traversable)

instance Show x => Show (StrictMono x) where
  show (StrictMono 0 m) = show m
  show (StrictMono n m) = let a = "2^" ++ show n
                              b = show (2 ^ n :: Int)
                          in minimumBy (comparing length) [b,a] ++ " * " ++ show m

data Monotone x
 = Linear x
 | Full (StrictMono x)
 deriving (Eq, Foldable, Functor, Traversable)

instance Show x => Show (Monotone x) where
  show (Linear v) = show v
  show (Full sm) = "(2^(" ++ show sm ++ ") - 1)"

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
    full n = 2 ^ n - 1

  numValue = numValue . StrictMono 0

-- Actual semantics for NumValue types
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

-- EvenOrOdd attempts to do DivMod to a numval.
-- It shouldn't change the number of free variables
class EvenOrOdd (t :: Type -> Type) where
  -- When half t is (n, b), then t = 2*n+b. I.e. True means odd
  half :: t x -> Maybe (NumVal x, Bool)

instance EvenOrOdd NumVal where
  half (NumValue upshift grower) = case (upshift `divMod` 2, half grower) of
    ((up, 0), Just (n, False)) -> Just (nPlus up n, False)
    ((up, 0), Just (n, True))  -> Just (nPlus up n, True)
    ((up, 1), Just (n, False)) -> Just (nPlus up n, True)
    ((up, 1), Just (n, True))  -> Just (nPlus (up + 1) n, False)
    _ -> Nothing

instance EvenOrOdd Fun00 where
  half Constant0 = Just (nZero, False)
  half (StrictMonoFun sm) = half sm

instance EvenOrOdd StrictMono where
  half sm@StrictMono{..}
    | multBy2ToThe > 0 = Just (numValue (sm { multBy2ToThe = multBy2ToThe - 1 })
                              ,False)
    | otherwise = half monotone

instance EvenOrOdd Monotone where
  half _ = Nothing

data ValPat
 = VPVar
 | VPCon QualName [ValPat]
 | VPNum NumPat
 deriving Show

data NumPat
 = NP0
 | NP1Plus NumPat
 | NP2Times NumPat
 | NPVar
 deriving Show

numMatch :: Bwd (Val Z) -- Stuff we've already matched
         -> NumVal (VVar Z) -- Type argument
         -> NumPat -- Pattern to match against arg
         -> Either ErrorMsg (Bwd (Val Z))
numMatch zv arg NPVar = pure (zv :< VNum arg)
numMatch zv arg NP0
  | arg == nZero = pure zv
  | otherwise = Left $ NumMatchFail "0" (show arg)
numMatch zv arg@NumValue{upshift = upshift} (NP1Plus np)
  | upshift > 0 = numMatch zv (arg { upshift = upshift - 1 }) np
  | otherwise = Left $ NumMatchFail "1 + n" (show arg)
numMatch zv arg (NP2Times np)
  | Just (h, False) <- half arg
  = numMatch zv h np
  | otherwise = Left $ NumMatchFail "2 * n" (show arg)

valMatch :: Val Z -- Type argument
         -> ValPat -- Pattern to match against arg
         -> Either ErrorMsg (Some (Ny :* Valz))
valMatch val pat = bwdStack <$> valMatch' B0 val pat

valMatches :: [Val Z] -- Type argument
           -> [ValPat] -- Pattern to match against arg
           -> Either ErrorMsg (Some (Ny :* Valz))
valMatches vals pats = bwdStack <$> valMatches' B0 vals pats

-- internal version has an accumulator first arg
valMatch' :: Bwd (Val Z) -> Val Z -> ValPat -> Either ErrorMsg (Bwd (Val Z))
valMatch' zv arg VPVar = pure (zv :< arg)
valMatch' zv (VCon u args) (VPCon u' vps)
  | u == u' = valMatches' zv args vps
  | otherwise = Left $ ValMatchFail (show u') (show u)
valMatch' zv (VNum n) (VPNum np) = numMatch zv n np
valMatch' _ v vp = error $ "valMatch called on " ++ show v ++ " " ++ show vp

valMatches' :: Bwd (Val Z) -> [Val Z] -> [ValPat] -> Either ErrorMsg (Bwd (Val Z))
valMatches' zv [] [] = pure zv
valMatches' zv (v:vs) (p:ps) = do
  zv <- valMatch' zv v p
  valMatches' zv vs ps
valMatches' _ _ _ = Left $ InternalError "ragged lists in valMatches"

---------------------- Variable Renumbering (VarChanger) ----------------------
-- A `Thinning i j` embeds i things among j things.
data Thinning :: N -> N -> Type where
  ThNull :: Thinning Z Z
  ThKeep :: Thinning i j -> Thinning (S i) (S j)
  ThDrop :: Thinning i j -> Thinning i (S j)

thId :: Ny i -> Thinning i i
thId Zy = ThNull
thId (Sy n) = ThKeep (thId n)

thEmpty :: Ny i -> Thinning Z i
thEmpty Zy = ThNull
thEmpty (Sy n) = ThDrop (thEmpty n)

thCompose :: Thinning i j -> Thinning j k -> Thinning i k
thCompose th (ThDrop ph) = ThDrop (thCompose th ph)
thCompose (ThDrop th) (ThKeep ph) = ThDrop (thCompose th ph)
thCompose (ThKeep th) (ThKeep ph) = ThKeep (thCompose th ph)
thCompose ThNull ThNull = ThNull

inxThin :: Inx i -> Thinning i j -> Inx j
inxThin v (ThDrop th) = VS (inxThin v th)
inxThin VZ (ThKeep _) = VZ
inxThin (VS v) (ThKeep th) = VS (inxThin v th)


class DeBruijn (t :: N -> Type) where
  -- Change the scope of Inx variables
  changeVar :: VarChanger src tgt -> t src -> t tgt

-- Intended solely for use by the DeBruijn typeclass.
-- The two Nat parameters correspond to the src and tgt scope respectively
data VarChanger :: N -> N -> Type where
  InxToPar :: AddR out inn tot   -- Proof that src - tgt = out
           -> Stack Z End out    -- Ends for each variable in outer scope
           -> VarChanger tot inn -- Reduce the scope by changing outer vars
  ParToInx :: AddR out inn tot
           -> Stack Z End out    -- Ends for each outer variable we want to abstract (by matching on the End)
           -> VarChanger inn tot -- Expand scope by abstract outer Par variables
  Thinning :: Thinning src tgt
           -> VarChanger src tgt

weakenVC :: VarChanger src tgt -> VarChanger (S src) (S tgt)
weakenVC (InxToPar a stk) = InxToPar (AddS a) stk
weakenVC (ParToInx a stk) = ParToInx (AddS a) stk
weakenVC (Thinning th) = Thinning (ThKeep th)


instance DeBruijn VVar where
  changeVar (InxToPar a endz) (VInx v) = case outOrInn a v of
    Left out -> VPar (proj endz out)
    Right inn -> VInx inn
  changeVar (ParToInx a endz) (VPar e)
    | Just out <- findInx endz e = VInx (injOut a out)
  -- Need to update the scope of inner variables, since we're adding more outers
  changeVar (ParToInx a _) (VInx v) = VInx (injInn a v)
  changeVar (Thinning th) (VInx v) = VInx (inxThin v th)
  changeVar _ (VPar e) = VPar e


instance DeBruijn Val where
  changeVar vc (VNum n) = VNum (fmap (changeVar vc) n)
  changeVar vc (VCon c vs) = VCon c (changeVar vc <$> vs)
  changeVar vc (VApp v ss)
    = VApp (changeVar vc v) (changeVar vc <$> ss)
  changeVar vc (VLam sc) = VLam (changeVar (weakenVC vc) sc)
  changeVar vc (VFun Braty cty)
    = VFun Braty $ changeVar vc cty
  changeVar vc (VFun Kerny cty)
    = VFun Kerny $ changeVar vc cty

varChangerThroughRo :: VarChanger src tgt
                    -> Ro m src src'
                    -> Some (VarChanger src' -- VarChanger src' tgt'
                             :*
                             Ro m tgt -- Ro m tgt tgt'
                            )
-- Lift the scope of Ro from src -> src' to tgt -> tgt'
-- R0 enforces src = src', so we choose tgt' = tgt in our existential type
varChangerThroughRo vc R0 = Some (vc :* R0)
varChangerThroughRo vc (RPr (p,ty) ro {- src -> src' -}) = case changeVar vc {- src -> tgt -} ty of
  ty -> case varChangerThroughRo vc ro of
          Some (vc {- src' -> tgt' -} :* ro {- tgt -> tgt' -}) -> Some (vc :* RPr (p,ty) ro)
varChangerThroughRo vc {- src -> tgt -} (REx pk ro {- S src' -> src'' -})
  = case varChangerThroughRo (weakenVC vc) ro of
        Some (vc {- src'' -> tgt'' -} :* ro {- S tgt' -> tgt'' -}) -> Some (vc :* REx pk ro)

instance DeBruijn (FunTy m) where
  changeVar (vc {- srcIn -> tgtIn -}) (FunTy ps ri {- srcIn -> srcMid -} ro {- srcMid -> srcOut -}) = case varChangerThroughRo vc ri of
    Some {- tgtMid -} (vc {- srcMid -> tgtMid -} :* ri {- tgtIn -> tgtMid -}) -> case varChangerThroughRo vc ro of
      Some {- tgtOut -} (_vc {- srcOut -> tgtOut -} :* ro {- tgtMid -> tgtOut -}) -> FunTy ps ri ro

kernelNoBind :: Ro Kernel bot top -> bot :~: top
kernelNoBind R0 = Refl
kernelNoBind (RPr _ ro) = kernelNoBind ro

endVal' :: Modey m -> BinderType m -> End -> BinderVal m
endVal' Braty (Left Nat) e = VNum (nVar (VPar e))
endVal' Braty _ e = VApp (VPar e) B0
endVal' Kerny _ e = KVar (VPar e)

endVal :: TypeKind -> End -> Val Z
endVal k e = varVal k (VPar e)

varVal :: TypeKind -> VVar n -> Val n
varVal Nat v = VNum (nVar v)
varVal _ v = VApp v B0

data KernelVal :: N -> Type where
  KVar  :: VVar n -> KernelVal n
  KBit  :: Bool -> KernelVal n
  KNil  :: KernelVal n
  KCons :: KernelVal n -> KernelVal n -> KernelVal n
deriving instance Show (KernelVal n)

type FunVal m = FunTy m Z
--value :: Modey m -> FunVal m -> Val Z
--value = VFun

roTopM :: Modey m -> Ny bot -> Ro m bot top -> Ny top
roTopM Braty = roTop
roTopM Kerny = \ny ro -> case kernelNoBind ro of
  Refl -> ny

roTop :: Ny bot -> Ro Brat bot top -> Ny top
roTop ny R0 = ny
roTop ny (RPr _ ro) = roTop ny ro
roTop ny (REx _ ro) = roTop (Sy ny) ro

copyable :: Val Z -> Maybe Bool
copyable TQ = Just False
copyable TMoney = Just False
-- If it can be instantiated with something linear, we can't copy it!
copyable (VApp _ _) = Just False
copyable (TVec elem _) = copyable elem
copyable TBit = Just True
copyable _ = Nothing

stkLen :: Stack Z t tot -> Ny tot
stkLen S0 = Zy
stkLen (zx :<< _) = Sy (stkLen zx)

numValIsConstant :: NumVal (VVar Z) -> Maybe Integer
numValIsConstant (NumValue up Constant0) = pure up
numValIsConstant _ = Nothing
