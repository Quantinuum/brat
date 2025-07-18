module Brat.Syntax.Concrete where

import Data.List.NonEmpty

import Brat.FC
import Brat.QualName
import Brat.Syntax.Common
import Brat.Syntax.FuncDecl (FuncDecl(..))
import Brat.Syntax.Simple

type FAlias = TypeAliasF Flat
type FEnv = ([FDecl], [FAlias])

type FlatIO = TypeRowElem (WC Flat) (WC (KindOr Flat))

data FBody
  = FClauses (NonEmpty (WC Abstractor, WC Flat))
  | FNoLhs (WC Flat)
  | FUndefined
 deriving Show

type FDecl = FuncDecl [FlatIO] FBody
deriving instance Show FDecl

data Flat
 = FVar QualName
 | FHope
 | FApp (WC Flat) (WC Flat)
 | FJuxt (WC Flat) (WC Flat)
 | FThunk (WC Flat)
 | FCompose (WC Flat) (WC Flat)
-- Keep |> distinct from application to keep track of user's syntax choice.
-- Note that it's turned into an application during elaboration
 | FInto (WC Flat) (WC Flat)
 | FArith ArithOp (WC Flat) (WC Flat)
 | FLambda (NonEmpty (WC Abstractor, WC Flat))
 | FAnnotation (WC Flat) [FlatIO]
 | FLetIn (WC Abstractor) (WC Flat) (WC Flat)
 | FSimple SimpleTerm
 | FHole String
 | FCon QualName (WC Flat)
 | FEmpty
 | FPull [PortName] (WC Flat)
 -- We can get away with not elaborating type signatures in the short term
 | FFn (CType' FlatIO)
 | FKernel (CType' (TypeRowElem (WC Flat) (WC Flat)))
 | FUnderscore
 | FPass
 | FFanOut
 | FFanIn
 | FIdentity
 | FOf ({- number :: -}WC Flat) {- of -} ({- expr -}WC Flat)
 deriving Show
