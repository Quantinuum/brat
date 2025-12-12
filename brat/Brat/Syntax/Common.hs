module Brat.Syntax.Common (PortName,
                           Dir(..),
                           Kind(..),
                           Diry(..),
                           Kindy(..),
                           CType'(..),
                           Import(..),
                           ImportSelection(..),
                           Pattern(..),
                           Abstractor(..), occursInAbstractor,
                           TypeKind(..), KindOr,
                           showSig,
                           showRow,
                           NamedPort(..),
                           Src, Tgt,
                           OutPort(..), InPort(..),
                           pattern PNone,
                           pattern PSome,
                           pattern POnePlus,
                           pattern PTwoTimes,
                           pattern PZero,
                           pattern PNil,
                           pattern PCons,
                           pattern PTrue,
                           pattern PFalse,
                           Mode(..),
                           Modey(..),
                           End(..),
                           TypeRow,
                           TypeRowElem(..),
                           forgetPortName,
                           toTypeRow,
                           MODEY(..),
                           KINDY(..),
                           DIRY(..),
                           modily,
                           deModey,
                           ArithOp(..),
                           pattern Dollar,
                           pattern Star,
                           Precedence(..)
                          ) where

import Brat.FC
import Brat.QualName
import Brat.Syntax.Abstractor
import Brat.Syntax.Port

import Data.Bifunctor (first)
import Data.List (intercalate)
import Data.Kind (Type)
import Data.Type.Equality (TestEquality(..), (:~:)(..))

data Mode = Brat | Kernel deriving (Eq, Ord, Show)

data Modey :: Mode -> Type where
  Braty :: Modey Brat
  Kerny :: Modey Kernel

deriving instance Show (Modey m)

class MODEY (m :: Mode) where
  modey :: Modey m

instance MODEY Brat where
  modey = Braty

instance MODEY Kernel where
  modey = Kerny

class KINDY (k :: Kind) where
  kindy :: Kindy k

instance KINDY Noun where
  kindy = Nouny

instance KINDY UVerb where
  kindy = UVerby

instance KINDY KVerb where
  kindy = KVerby

-- `MODEY m` means that `m` is a Mode known at runtime
modily :: Modey m -> (MODEY m => t) -> t
modily Braty t = t
modily Kerny t = t

deModey :: Modey m -> Mode
deModey Braty = Brat
deModey Kerny = Kernel

instance TestEquality Modey where
  testEquality Braty Braty = Just Refl
  testEquality Kerny Kerny = Just Refl
  testEquality _ _ = Nothing

data TypeRowElem ty = Named PortName ty | Anon ty deriving (Foldable, Functor, Traversable)
type TypeRow ty = [TypeRowElem ty]

forgetPortName :: TypeRowElem ty -> ty
forgetPortName (Anon ty) = ty
forgetPortName (Named _ ty) = ty

toTypeRow :: [(String, ty)] -> TypeRow ty
toTypeRow = fmap (uncurry Named)

instance Show ty => Show (TypeRowElem ty) where
  show (Named p ty) = p ++ " :: " ++ show ty
  show (Anon ty) = show ty

instance Eq ty => Eq (TypeRowElem ty) where
  Named _ ty == Named _ ty' = ty == ty'
  Anon ty == Named _ ty' = ty == ty'
  Named _ ty == Anon ty' = ty == ty'
  Anon ty == Anon ty' = ty == ty'

data TypeKind = TypeFor Mode [(PortName, TypeKind)] | Nat
  deriving (Eq, Ord)

instance Show TypeKind where
  show (TypeFor m args) = let argsStr = if null args then "" else "(" ++ intercalate ", " (show <$> args) ++ ")"
                              kindStr = case m of
                                Brat -> "*"
                                Kernel -> "$"
                          in kindStr ++ argsStr
  show Nat = "#"

pattern Star, Dollar :: [(PortName, TypeKind)] -> TypeKind
pattern Star ks = TypeFor Brat ks
pattern Dollar ks = TypeFor Kernel ks

type KindOr = Either TypeKind

instance {-# OVERLAPPING #-} Show a => Show (KindOr a) where
  show (Left k) = show k
  show (Right ty) = show ty

-- How to typecheck the *outputs* of a term
data Dir = Syn -- the node synthesizes (tells us) its outputs
         | Chk -- the node must be told the type of its outputs
   deriving (Eq, Show)

data Diry :: Dir -> Type where
  Syny :: Diry Syn
  Chky :: Diry Chk
deriving instance Show (Diry d)

class DIRY (d :: Dir) where
  diry :: Diry d

instance DIRY Chk where
  diry = Chky

instance DIRY Syn where
  diry = Syny

-- How to typecheck the *inputs* of a term
data Kind = Noun -- there are no inputs
          | UVerb -- a verb with unknown inputs, i.e. it must be told the type of its inputs (it knows how many to take)
          | KVerb -- a verb with known inputs, i.e. it synthesizes (tells us) the number and type of inputs it needs
   deriving (Eq, Show)

data Kindy :: Kind -> Type where
  Nouny :: Kindy Noun
  UVerby :: Kindy UVerb
  KVerby :: Kindy KVerb
deriving instance Show (Kindy k)

data CType' io = [io] :-> [io] deriving (Foldable, Functor, Traversable)

instance Show io => Show (CType' io) where
  show (ss :-> ts) = unwords [show ss, "->", show ts]

deriving instance Eq io => Eq (CType' io)

instance Semigroup (CType' (PortName, ty)) where
  (ss :-> ts) <> (us :-> vs) = (ss <> us) :-> (ts <> vs)

data Import
  = Import { importName :: WC QualName
           , importQualified :: Bool
           , importAlias :: Maybe (WC String)
           , importSelection :: ImportSelection
           }
  deriving (Eq, Ord)

data ImportSelection
  = ImportAll
  | ImportPartial [WC String]
  | ImportHiding [WC String]
  deriving (Eq, Ord)

instance Show Import where
  show Import{..} =
    let prefix = if importQualified then [] else ["open"]
        alias = maybe [] (\x -> ["as",unWC x]) importAlias
    in  unwords . concat $ [prefix,[show (unWC importName)],alias,showSelection importSelection]
   where
    showSelection ImportAll = []
    showSelection (ImportPartial fns) = "(":(unWC <$> fns) ++ [")"]
    showSelection (ImportHiding fns) = "hiding (":(unWC <$> fns) ++ [")"]

showSig :: Show ty => [(String, ty)] -> String
showSig [] = "()"
showSig (x:xs)
  = intercalate ", " [ '(':p ++ " :: " ++ show ty ++ ")"
                     | (p, ty) <- x:xs]

showRow :: Show ty => [(NamedPort e, ty)] -> String
showRow = showSig . fmap (first portName)


data ArithOp = Add | Sub | Mul | Div | Pow deriving (Eq, Show)

-- Operator precedence for non-atomic expressions
-- First constructor (=0) has loosest binding
data Precedence
 = PLetIn
 | PLambda
 | PInto
 | PComp
 | PJuxtPull -- Juxtaposition has the same precedence as port pulling
 | PVecPat
 | POf
 | PAddSub
 | PMulDiv
 | PPow
 | PAnn
 | PApp
 deriving (Bounded, Enum, Eq, Ord, Show)
