module Brat.Unelaborator (unelab) where

import Brat.FC (WC(..), dummyFC, unWC)
import Brat.Syntax.Concrete (Flat(..))
import Brat.Syntax.Common (Dir(..), Kind(..), Diry(..), Kindy(..)
                          ,KindOr, TypeRowElem(..), CType'(..)
                          )
import Brat.Syntax.Core (Term(..))

import Data.Bifunctor (second)
import Data.List.NonEmpty (NonEmpty(..))

unelab :: Diry d -> Kindy k -> Term d k -> Flat
unelab _ _ (Simple tm) = FSimple tm
unelab dy ky (Let abs expr body) = FLetIn abs (unelab Syny Nouny <$> expr) (unelab dy ky <$> body)
unelab _ _ (NHole name) = FHole (show name)
unelab _ _ (VHole name) = FHole (show name)
unelab _ _ Empty = FEmpty
unelab dy ky (a :|: b) = FJuxt (unelab dy ky <$> a) (unelab dy ky <$> b)
unelab _ _ Pass = FPass
unelab _ _ (Th thunk) = FThunk (unelab Chky UVerby <$> thunk)
unelab _ _ (TypedTh thunk) = FThunk (unelab Syny KVerby <$> thunk)
unelab _ _ (Force tm) = unelab Syny Nouny (unWC tm)
unelab _ ky (Emb tm) = unelab Syny ky (unWC tm)
unelab dy _ (Forget tm) = unelab dy KVerby (unWC tm)
unelab _ ky (Pull ps tm) = FPull ps (unelab Chky ky <$> tm)
unelab _ _ (Var v) = FVar v
unelab dy ky (Arith op lhs rhs) = FArith op (unelab dy ky <$> lhs) (unelab dy ky <$> rhs)
unelab dy _ (Of n e) = FOf (unelab Chky Nouny <$> n) (unelab dy Nouny <$> e)
unelab _ _ (tm ::: outs) = FAnnotation (unelab Chky Nouny <$> tm) (f outs)
 where
  f :: [TypeRowElem (KindOr (Term Chk Noun))] -> [TypeRowElem (WC (KindOr Flat))]
  f = fmap (fmap (dummyFC . fmap (unelab Chky Nouny)))
unelab dy ky (top :-: bot) = case ky of
  Nouny -> FInto (unelab Syny Nouny <$> top) (unelab dy UVerby <$> bot)
  _ -> FApp (unelab Syny ky <$> top) (unelab dy UVerby <$> bot)
unelab dy ky (f :$: s) = FApp (unelab dy KVerby <$> f) (unelab Chky ky <$> s)
unelab dy _ (Lambda (abs,rhs) cs) = FLambda ((abs, unelab dy Nouny <$> rhs) :| (second (fmap (unelab Chky Nouny)) <$> cs))
unelab _ _ (Con c args) = FCon c (unelab Chky Nouny <$> args)
unelab _ _ (C (ss :-> ts)) = FFn ((unelabRo ss)
                                  :->
                                  (unelabRo ts)
                                 )
unelab _ _ (K (ss :-> ts)) = FKernel (unelabKernRo ss :-> unelabKernRo ts)
unelab _ _ Identity = FIdentity
unelab _ _ (Hope ident) = FHope ident
unelab _ _ FanIn = FFanIn
unelab _ _ FanOut = FFanOut

unelabKernRo :: [TypeRowElem (Term Chk Noun)] -> [TypeRowElem (WC Flat)]
unelabKernRo = fmap (fmap (dummyFC . unelab Chky Nouny))

unelabRo :: [(TypeRowElem (KindOr (Term Chk Noun)))] -> [TypeRowElem (WC (KindOr Flat))]
unelabRo = fmap (fmap (dummyFC . fmap (unelab Chky Nouny)))
