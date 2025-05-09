module Brat.Syntax.Core (Term(..)
                        ,Input
                        ,Output
                        ,InOut
                        ,CType
                        ,CoreFuncDecl
                        ,Precedence(..)
                        ,precedence
                        ) where

import Brat.Constructors.Patterns (pattern CCons,
                                   pattern CSnoc,
                                   pattern CConcatEqEven,
                                   pattern CConcatEqOdd,
                                   pattern CRiffle)
import Brat.FC
import Brat.Naming
import Brat.QualName
import Brat.Syntax.CircuitProperties
import Brat.Syntax.Common
import Brat.Syntax.FuncDecl
import Brat.Syntax.Simple

import Data.Kind (Type)
import Data.Maybe (fromJust)

type Input = InOut
type Output = InOut
type InOut = (PortName, KindOr (Term Chk Noun))

type CType = CType' InOut

type CoreFuncDecl = FuncDecl [InOut] (FunBody Term Noun)

data Term :: Dir -> Kind -> Type where
  Simple   :: SimpleTerm -> Term Chk Noun
  Let      :: WC Abstractor -> WC (Term Syn Noun) -> WC (Term d k) -> Term d k
  -- Takes pair of a user provided mnemonic and a unique name
  NHole    :: (String, Name) -> Term Chk Noun
  VHole    :: (String, Name) -> Term Chk UVerb
  Pass     :: Term Syn UVerb
  Empty    :: Term Chk Noun -- The empty row (monoidal unit of :|:)
  -- Parallel composition, aka juxtaposition
  (:|:)    :: WC (Term d k) -> WC (Term d k) -> Term d k
  Th       :: WC (Term Chk UVerb) -> Term Chk Noun
  TypedTh  :: WC (Term Syn KVerb) -> Term Syn Noun
  Force    :: WC (Term Syn Noun) -> Term Syn KVerb
  Emb      :: WC (Term Syn k) -> Term Chk k
  Forget   :: WC (Term d KVerb) -> Term d UVerb
  Pull     :: [PortName] -> WC (Term Chk k) -> Term Chk k
  Var      :: QualName -> Term Syn Noun  -- Look up in noun (value) env
  Identity :: Term Syn UVerb
  Hope     :: Term Chk Noun
  Arith    :: ArithOp -> WC (Term Chk Noun) -> WC (Term Chk Noun) -> Term Chk Noun
  Of       :: WC (Term Chk Noun) -> WC (Term d Noun) -> Term d Noun

  -- Type annotations (annotating a term with its outputs)
  (:::)    :: WC (Term Chk Noun) -> [Output] -> Term Syn Noun
  -- Composition: values fed from source (first) into dest (second),
  -- of number/type determined by the source
  (:-:)    :: WC (Term Syn k) -> WC (Term d UVerb) -> Term d k
  -- Application of function (first) to values coming from argument (second)
  -- of number/type determined by the function. (aka, Reverse Composition)
  (:$:)    :: WC (Term d KVerb) -> WC (Term Chk k) -> Term d k
  -- Lambda that matches over a series of patterns.
  -- In `Syn`, for now, the first clause provides the type.
  Lambda   :: (WC Abstractor, WC (Term d Noun)) -> [(WC Abstractor, WC (Term Chk Noun))] -> Term d UVerb
  -- Type constructors
  Con      :: QualName -> WC (Term Chk Noun) -> Term Chk Noun
  -- Brat function types
  C        :: CType' (PortName, KindOr (Term Chk Noun)) -> Term Chk Noun
  -- Kernel types
  K        :: Properties Kernel ->  CType' (PortName, Term Chk Noun) -> Term Chk Noun
  FanOut   :: Term Syn UVerb
  FanIn    :: Term Chk UVerb

deriving instance Eq (Term d k)

-- N.B. The effort going into making a nice show instance for Term should also
-- go into the Show instance for Flat, which should be the user facing format,
-- constructed using `unelaborate`
instance Show (Term d k) where
  show (Simple tm) = show tm
  show (Let abs xs body)
    = unwords ["let", show abs, "=", show xs, "in", show body]
  show (NHole (name, _)) = '?' : name
  show (VHole (name, _)) = '?' : name
  show Empty = "()"
  show (a :|: b) = bracket PJuxtPull a ++ ", " ++ bracket PJuxtPull b
  show Pass = "pass"
  show (Th comp) = '{' : show comp ++ "}"
  show (TypedTh comp) = "{:" ++ show comp ++ ":}"
  show (Force th) = show th ++ "()"
  show (Forget kv) = "(Forget " ++ show kv ++ ")"
  show (Emb x) = '「' : show x ++ "」"
  show tm@(Arith op lhs rhs) = let prec = fromJust (precedence tm) in
                                 unwords [bracket prec lhs
                                         ,showOp op
                                         -- Arith ops are left nested, so call
                                         -- the rhs with `prec + 1`
                                         ,bracket (succ prec) rhs
                                         ]
   where
    showOp = \case
      Add -> "+"
      Mul -> "*"
      Pow -> "^"
      Sub -> "-"
      Div -> "/"
  show (Pull ps x) = showList ps ++ bracket PJuxtPull x
   where
    showList [] = "[]:"
    showList ps = concatMap (++":") ps
  show (Of n e) = unwords [bracket POf n
                          ,"of"
                          ,bracket POf e
                          ]

  show (Var x) = show x
  show Identity = "|"
  show Hope = "!"
  -- Nested applications should be bracketed too, hence 4 instead of 3
  show (fun :$: arg) = bracket PApp fun ++ ('(' : show arg ++ ")")
  show (tm ::: ty) = bracket PAnn tm ++ " :: " ++ show ty
  show (a :-: b) = bracket PComp a ++ "; " ++ bracket PComp b
  show (Lambda c cs) = unlines (showClause c : (("| "++) . showClause <$> cs))
   where
    showClause (xs, bod) = show xs ++ " => " ++ bracket PLambda bod
  show p@(Con c arg) = case prettyPat p of
    Just ps -> show ps
    Nothing -> {-case unWC arg of
      Empty -> show c
      _ -> -}show c ++ "(" ++ show arg ++ ")"
   where
    prettyPat :: Term Chk Noun -> Maybe [Term Chk Noun]
    prettyPat (Con (PrefixName [] "nil") (WC _ Empty)) = Just []
    prettyPat (Con (PrefixName [] "cons") (WC _ (x :|: xs))) = (unWC x :) <$> prettyPat (unWC xs)
    prettyPat _ = Nothing

  show (C f) = "{" ++ show f ++ "}"
  show (K _ (ss :-> ts)) = "{" ++ showSig ss ++ " -o " ++ showSig ts ++ "}"
  show FanOut = "[/\\]"
  show FanIn = "[\\/]"


-- Wrap a term in brackets if its `precedence` is looser than `n`
bracket :: Precedence -> WC (Term d k) -> String
bracket n (WC _ tm) = case precedence tm of
  Just m | m < n -> '(' : show tm ++ ")"
  _ -> show tm

-- Report tightness of binding, or `Nothing` if not a binary op
precedence :: Term d k -> Maybe Precedence
precedence (Let {})  = Just PLetIn
precedence (Lambda _ _) = Just PLambda
precedence (_ :-: _)    = Just PComp
precedence (Pull _ _)   = Just PJuxtPull
precedence (_ :|: _)    = Just PJuxtPull
precedence (Con c _)
  | c `elem` [CCons,CSnoc,CConcatEqEven,CConcatEqOdd,CRiffle] = Just PVecPat
precedence (_ :$: _)    = Just PApp
precedence (_ ::: _)    = Just PAnn
precedence (Of _ _)     = Just POf
precedence (Arith op _ _) = Just $ case op of
  Add -> PAddSub
  Sub -> PAddSub
  Div -> PMulDiv
  Mul -> PMulDiv
  Pow -> PPow
precedence _ = Nothing
