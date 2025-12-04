{-# LANGUAGE QuantifiedConstraints #-}
module Hasochism where

import Data.Kind (Type)
import Data.Type.Equality (TestEquality(..), (:~:)(..))

data N = Z | S N
data Ny :: N -> Type where
  Zy :: Ny Z
  Sy :: Ny n -> Ny (S n)

ny2int :: Ny n -> Int
ny2int Zy = 0
ny2int (Sy n) = 1 + ny2int n

integer2Ny :: Integer -> Some Ny
integer2Ny 0 = Some Zy
integer2Ny n | n > 0 = case integer2Ny (n - 1) of Some x -> Some (Sy x)
integer2Ny _ = error "integer2Ny: negative"

instance TestEquality Ny where
  testEquality Zy Zy = Just Refl
  testEquality (Sy n) (Sy m) | Just Refl <- testEquality n m = Just Refl
  testEquality _ _ = Nothing

data Some (t :: a -> Type) :: Type where
  -- Stashing some a
  Some :: t a -> Some t
deriving instance (forall n. Show (t n)) => Show (Some t)

data (:*) (l :: a -> Type) (r :: a -> Type) :: a -> Type where
  (:*) :: l a -> r a -> (l :* r) a

newtype Flip (t :: a -> b -> Type) (y :: b) (x :: a)
  = Flip { getFlip :: t x y }

instance Show (t a b) => Show (Flip t b a) where
  show = show . getFlip

-- Not to be confused with AddR in Value.hs where the arguments are flipped
data AddL :: N -> N -> N -> Type where
  AddLZ :: Ny out -> AddL Z out out
  AddLS :: AddL inn out tot -> AddL (S inn) out (S tot)

data MulL :: N -> N -> N -> Type where
  MulLZ :: Ny inn -> MulL inn Z Z
  MulLS :: MulL inn mul prd -> AddL inn prd tot -> MulL inn (S mul) tot

addL :: Ny l -> Ny r -> Some (AddL l r)
addL Zy out = Some (AddLZ out)
addL (Sy inn) out = case addL inn out of Some tot -> Some (AddLS tot)

addTot :: AddL l r t -> Ny t
addTot (AddLZ out) = out
addTot (AddLS a) = Sy (addTot a)

mulTot :: MulL l r t -> Ny t
mulTot (MulLZ _) = Zy
mulTot (MulLS _ a) = addTot a

mulL :: Ny l -> Ny r -> Some (MulL l r)
mulL inn Zy = Some (MulLZ inn)
mulL inn (Sy mul) = case mulL inn mul of Some prd -> case addL inn (mulTot prd) of Some tot -> Some (MulLS prd tot)

