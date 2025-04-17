{-# LANGUAGE UndecidableInstances #-}

module Brat.Checker.Types (Overs, Unders
                          ,Outputs, Inputs
                          ,ChkConnectors, SynConnectors
                          ,Mode(..), Modey(..)
                          ,Env, VEnv, KEnv, EnvData
                          ,Store(..), EndType(..)
                          ,emptyEnv
                          ,TypedHole(..), HoleTag(..), HoleData(..)
                          ,initStore
                          ,kindForMode
                          ) where

import Brat.Checker.Quantity
import Brat.FC (FC)
import Brat.Naming (Name)
import Brat.QualName (QualName)
import Brat.Syntax.Common
import Brat.Syntax.Value
import Hasochism (N(..))

import Data.Kind (Type)
import qualified Data.Map as M

-- Inputs against which a term is checked
type family Overs (m :: Mode) (k :: Kind) :: Type where
  Overs m Noun = ()
  Overs m UVerb = [(Src, BinderType m)]
  Overs m KVerb = ()

-- Inputs synthesized by the term
type family Inputs (m:: Mode) (k :: Kind) :: Type where
  Inputs m Noun = ()
  Inputs m UVerb = ()
  Inputs m KVerb = [(Tgt, BinderType m)]

-- Outputs against which a term is checked
type family Unders (m :: Mode) (d :: Dir) :: Type where
  Unders m Syn = ()
  Unders m Chk = [(Tgt, BinderType m)]

-- Outputs synthesized by the term
type family Outputs (m :: Mode) (d :: Dir) :: Type where
  Outputs m Syn = [(Src, BinderType m)]
  Outputs m Chk = ()

type ChkConnectors (m :: Mode) (d :: Dir) (k :: Kind) = (Overs m k, Unders m d)
type SynConnectors (m :: Mode) (d :: Dir) (k :: Kind) = (Inputs m k, Outputs m d)

type family EnvData (m :: Mode) where
  -- Brat variables can stand for rows when referring to a top level
  -- binding. Most of the time, this will be a singleton list
  EnvData Brat = [(Src, BinderType Brat)]
  EnvData Kernel = (Quantity, (Src, BinderType Kernel))

type Env e = M.Map QualName e
type VEnv = Env (EnvData Brat)
type KEnv = Env (EnvData Kernel)

emptyEnv :: Env a
emptyEnv = M.empty

data HoleTag :: Mode -> Kind -> Type where
  NBHole :: HoleTag Brat Noun
  NKHole :: HoleTag Kernel Noun
  VBHole :: HoleTag Brat UVerb
  VKHole :: HoleTag Kernel UVerb

data TypedHole where
  TypedHole :: HoleTag m k -> HoleData (ChkConnectors m Chk k) -> TypedHole

data HoleData a = HoleData
  { mnemonic :: String -- The name the user gave
  , name :: Name -- The name BRAT gave
  , fc :: FC
  , suggestions :: Maybe [String] -- Nothing means we didn't try
  , connectors :: a
  }

instance ShowWithMetas TypedHole where
  showWithMetas m (TypedHole tag dat) = ((('?' : mnemonic dat) ++ " :: ") ++) $
    case (tag, connectors dat) of
      (NBHole, ((), unders)) -> showRow m unders
      (NKHole, ((), unders)) -> showRow m unders
      (VBHole, (overs, unders)) -> "{ " ++ showRow m overs ++ " -> " ++ showRow m unders ++ " }"
      (VKHole, (overs, unders)) -> "{ " ++ showRow m overs ++ " -o " ++ showRow m unders ++ " }"

data EndType where
  EndType :: Modey m -> BinderType m -> EndType

instance Show EndType where
  show (EndType Kerny ty) = show ty
  show (EndType Braty (Left k)) = show k
  show (EndType Braty (Right ty)) = show ty

data Store = Store
  { typeMap    :: M.Map End EndType
  , valueMap   :: M.Map End (Val Z)
  , userNames  :: M.Map End String
  }

instance Show Store where
  show (Store km vm nm) = unlines $
                       ("Kinds:":(showKind <$> M.toList km))
                       ++ ("\nValues:":(showVal <$> M.toList vm)
                       ++ ("\nNames:":(show <$> M.toList nm)))
   where
    showKind (key, kind) = show key ++ " :: " ++ show kind
    showVal (key, val) = show key ++ " = " ++ show val

initStore :: Store
initStore = Store M.empty M.empty M.empty

instance Semigroup Store where
  (Store ks vs nm) <> (Store ks' vs' nm') = Store (ks <> ks') (vs <> vs') (nm <> nm')

kindForMode :: Modey m -> TypeKind
kindForMode Braty = Star []
kindForMode Kerny = Dollar []
