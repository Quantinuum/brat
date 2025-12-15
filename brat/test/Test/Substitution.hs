module Test.Substitution where

import Test.Tasty

{-
-- TODO: update to value scopes syntax
import Brat.Checker.Monad
import Brat.Checker.SolveHoles
import Brat.Checker.Types
import Brat.Error
import Brat.Naming
import Brat.QualName
import Brat.Syntax.Common
import Brat.Syntax.Value
import Bwd
import Control.Monad.Freer
import Hasochism

import Test.Util (runEmpty)

import Data.Bifunctor
import Test.Tasty.HUnit

node = fst (fresh "" root)

-- Comparing type equality for rows is only exposed via checking equality of function types
chk ss ts = typeEq "" (Row) ss ts

var :: VVar n -> Val n
var v = VApp v B0

vpar :: Val n
vpar v = VApp v B0

checkSigs :: Checking (Ro m i j, Ro m i j) -> Assertion
checkSigs x = case runEmpty (x >>= \(ss, ts) -> chk ss ts) of
  Right _ -> pure ()
  Left e -> assertFailure (showError e)

-- Instantiate both x and n into
-- (xs :: Vec(x, n))
inst = testCase "instantiation" $ checkSigs $ do
  req $ Declare x (Star [])
  req $ Declare n Nat
  pure ([("xs", exp)],[("xs", act)])
 where
  x = ExEnd (Ex node 0)
  n = ExEnd (Ex node 1)
  exp = Right $ TVec (vpar x) (vpar n)
  act = Right $ changeVar (InxToPar (AddZ (Sy (Sy Zy))) (S0 :<< x :<< n)) $
        TVec (var (VInx 1)) (var (VInx 0))

-- a version of `inst` on a row with no binding
-- (xs :: Vec(x, n), ys :: Vec(x, n))
insts = testCase "instantiations" $ checkSigs $ do
  req $ Declare x (Star [])
  req $ Declare n Nat
  pure ([("xs", exp),("ys", exp)], act)
 where
  x = ExEnd (Ex node 0)
  n = ExEnd (Ex node 1)
  exp = Right $ TVec (var (VPar x)) (var (VPar n))
  act = changeVar (InxToPar (AddZ (Sy (Sy Zy))) (S0 :<< x :<< n)) $
        RPr ("xs", TVec (var (VInx 1)) (var (VInx 0))) (RPr ("ys", TVec (var (VInx 1)) (var (VInx 0))) R0)

-- Substitution doesn't affect local bindings
localBinding = testCase "localBinding" $ checkSigs $ do
  req $ Declare x (Star [])
  req $ Declare n Nat
  pure (exp, act)
 where
  x = ExEnd (Ex node 0)
  n = ExEnd (Ex node 1)
  -- Assuming x and n have already been bound:
  -- (xs :: Vec(x, n), m :: #, ys :: Vec(x, m), zs :: Vec(x, n))
  exp :: Ro Brat Z (S Z)
  exp = RPr ("xs", TVec (var (VPar x)) (var (VPar n)))
        (REx ("m",  Nat) (S0 ::-
          (RPr ("ys", TVec (var (VPar x)) (var (VInx 0)))
           (RPr ("zs", TVec (var (VPar x)) (var (VPar n)))
            R0))))

  act :: Ro Brat Z (S Z)
  act = changeVar (InxToPar (AddZ (Sy (Sy Zy))) (S0 :<< x :<< n)) unsubd

  unsubd :: Ro Brat (S (S Z)) (S (S (S Z)))
  unsubd = RPr ("xs", TVec (var (VInx 1)) (var (VInx 0)))
           (REx ("m", Nat)
            (S0 ::-
             (RPr ("ys", TVec (var (VInx 2)) (var (VInx 0)))
              (RPr ("zs", TVec (var (VInx 2)) (var (VInx 1)))
               R0))))

-- subst and insert both act on this signature
sig = REx ("X", Star [])
      (S0 ::-
       (RPr ("x5", TVec (VApp (VInx 0) B0) (VNum (nConstant 5)))
        (REx ("n", Nat)
         (S0 ::-
          (RPr ("xn", TVec (VApp (VInx 1) B0) (VApp (VInx 0) B0))
           R0
          )))))

{- What do these do?
-- Replace "X" with "Y" in sig
subst = testCase "subst" $ checkSigs (pure (exp, act))
 where
  x = ExEnd (Ex node 0)
  n = ExEnd (Ex node 1)
  inxd = changeVar (InxToPar (AddZ (Sy (Sy Zy))) (S0 :<< x :<< n)) sig
  insd = let (x:rest) = inxd in (("Y",Left (Star [])):rest)
  act = changeVar (ParToInx (AddR (AddR (AddZ Zy))) (S0 :<< x :<< n)) insd
  exp = let (x:rest) = sig in ("Y",Left (Star [])):rest

-- Insert "Y" into the middle of sig
insert = testCase "insert" $ checkSigs (pure (exp, act))
 where
  x = ExEnd (Ex node 0)
  n = ExEnd (Ex node 1)
  y = ExEnd (Ex node 2)
  inxd = changeVars (InxToPar (S0 :<< x :<< n)) sig
  insd = let (x:rest) = inxd in (x:("Y",Left (Star [])):rest)
  act = changeVars (ParToInx (S0 :<< x :<< y :<< n)) insd
  exp = let (x:rest) = sig in x:("Y",Left (Star [])):rest

  chk [] = pure ()
  chk ((Left k, Left k'):rest) = case kindEq k k' of
    Left msg -> err msg
    Right _ -> chk rest
  chk ((Right s, Right t):rest) = typeEq "" (Star []) s t *> chk rest
  chk _ = typeErr ""
-}

nullSubst = testCase "nullSubst" $
  case runEmpty test of
    Right _ -> if (show exp == show act)
               then pure ()
               else assertFailure $
                    unlines ["Lexical difference in terms:"
                            ,"Expected: " ++ show exp
                            ,"Actual: " ++ show act
                            ]
    Left e -> assertFailure (showError e)
 where
  test = typeEq "X -> [X,X]" (Star [("X", Star [])]) exp act

  exp = VLam (S0 ::- (VCon (plain "cons") [var (VInx 0), VCon (plain "cons") [var (VInx 0), VCon (plain "nil") []]]))
  act = changeVar (InxToPar (AddZ Zy) S0) exp
-}

substitutionTests = testGroup "Substitution" [] -- [inst, insts, localBinding, subst, insert, nullSubst]
