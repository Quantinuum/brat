module Brat.Checker.SolveHoles (typeEq, typesEq) where

import Brat.Checker.Helpers (mineToSolve, solveSem)
import Brat.Checker.Monad
import Brat.Checker.SolveNumbers
import Brat.Checker.Types (kindForMode)
import Brat.Error (ErrorMsg(..))
import Brat.Eval
import Brat.Naming (FreshMonad(..))
import Brat.Syntax.Common
-- import Brat.Syntax.Simple (SimpleTerm(..))
import Brat.Syntax.Value
import Control.Monad.Freer
import Bwd
import Hasochism
-- import Brat.Syntax.Port (toEnd)

import Control.Monad (unless)
import Data.Bifunctor (second)
import Data.Foldable (sequenceA_)
import Data.Functor
import qualified Data.Set as S
import Data.Type.Equality (TestEquality(..), (:~:)(..))

-- Demand that two closed values are equal, we're allowed to solve variables in the
-- hope set to make this true.
-- Raises a user error if the vals cannot be made equal.
typeEq :: String -- String representation of the term for error reporting
       -> TypeKind -- The kind we're comparing at
       -> Val Z -- Expected
       -> Val Z -- Actual
       -> Checking ()
typeEq str k exp act = do
  prefix <- whoAmI
  trackM ("typeEq: Who am I: " ++ show prefix)
  typeEq' str (Zy :* S0 :* S0) k exp act

typesEq :: String -- String representation of the term for error reporting
        -> [TypeKind] -- The kinds we're comparing at
        -> [Val Z] -- Expected
        -> [Val Z] -- Actual
        -> Checking ()
typesEq str k exp act = do
  prefix <- whoAmI
  trackM ("typesEq: Who am I: " ++ show prefix)
  typeEqs str (Zy :* S0 :* S0) k exp act


-- Internal version of typeEq with environment for non-closed values
typeEq' :: String -- String representation of the term for error reporting
        -> (Ny :* Stack Z TypeKind :* Stack Z Sem) n
        -> TypeKind -- The kind we're comparing at
        -> Val n -- Expected
        -> Val n -- Actual
        -> Checking ()
typeEq' str stuff@(ny :* _ks :* sems) k exp act = do
  mine <- mineToSolve
  exp <- sem sems exp
  act <- sem sems act
  qexp <- quote ny exp
  qact <- quote ny act
  trackM ("typeEq' exp: " ++ show qexp)
  trackM ("typeEq' act: " ++ show qact)
  typeEqEta str stuff mine k exp act

-- Presumes that the hope set and the two `Sem`s are up to date.
typeEqEta :: String -- String representation of the term for error reporting
          -> (Ny :* Stack Z TypeKind :* Stack Z Sem) n
          -> (End -> Maybe String) -- Tells us if we can solve a given End
          -> TypeKind -- The kind we're comparing at
          -> Sem -- Expected
          -> Sem -- Actual
          -> Checking ()
typeEqEta tm (lvy :* kz :* sems) mine (TypeFor m ((_, k):ks)) exp act = do
  -- Higher kinded things
  let nextSem = semLvl lvy
  let xz = B0 :< nextSem
  exp <- applySem exp xz
  act <- applySem act xz
  typeEqEta tm (Sy lvy :* (kz :<< k) :* (sems :<< nextSem)) mine (TypeFor m ks) exp act
-- Not higher kinded - check for flex terms
-- (We don't solve under binders for now, so we only consider Zy here)
-- 1. "easy" flex cases
typeEqEta _tm (Zy :* _ks :* _sems) mine k (SApp (SPar e) B0) act
  | Just _ <- mine e = solveSem k e act
typeEqEta _tm (Zy :* _ks :* _sems) mine k exp (SApp (SPar e) B0)
  | Just _ <- mine e = solveSem k e exp
typeEqEta _ (Zy :* _ :* _) mine Nat (SNum exp) (SNum act) = unifyNum mine (quoteNum Zy exp) (quoteNum Zy act)
-- 2. harder cases, neither is in the hope set, so we can't define it ourselves
typeEqEta tm stuff@(ny :* _ks :* _sems) _ k exp act = do
  exp <- quote ny exp
  act <- quote ny act
  unless (exp == act) $ case flexes act ++ flexes exp of
    [] -> typeEqRigid tm stuff k exp act -- easyish, both rigid i.e. already defined
    -- tricky: must wait for one or other to become more defined
    es -> mkYield "typeEqEta" (S.fromList es) >> typeEq' tm stuff k exp act

typeEqs :: String -> (Ny :* Stack Z TypeKind :* Stack Z Sem) n -> [TypeKind] -> [Val n] -> [Val n] -> Checking ()
typeEqs _ _ [] [] [] = pure ()
typeEqs tm stuff (k:ks) (exp:exps) (act:acts) = do
  mkFork "typeEqsTail" $ typeEqs tm stuff ks exps acts
  typeEq' tm stuff k exp act
typeEqs _ _ _ _ _ = typeErr "arity mismatch"

typeEqRow :: Modey m
          -> String -- The term we complain about in errors
          -> (Ny :* Stack Z TypeKind :* Stack Z Sem) lv -- Next available level, the kinds of existing levels
          -> Ro m lv top0
          -> Ro m lv top1
          -> Either ErrorMsg (Some ((Ny :* Stack Z TypeKind :* Stack Z Sem) -- The new stack of kinds and fresh level
                                   :* ((:~:) top0 :* (:~:) top1)) -- Proofs both input rows have same length (quantified over by Some)
                             ,[Checking ()] -- subproblems to run in parallel
                             )
typeEqRow _ _ stuff R0 R0 = pure (Some (stuff :* (Refl :* Refl)), [])
typeEqRow m tm stuff (RPr (_,ty1) ro1) (RPr (_,ty2) ro2) = typeEqRow m tm stuff ro1 ro2 <&> second
  ((:) (typeEq' tm stuff (kindForMode m) ty1 ty2))
typeEqRow m tm (ny :* kz :* semz) (REx (_,k1) ro1) (REx (_,k2) ro2) | k1 == k2 = typeEqRow m tm (Sy ny :* (kz :<< k1) :* (semz :<< semLvl ny)) ro1 ro2
typeEqRow _ _ _ _ _ = Left $ TypeErr "Mismatched rows"

-- Calls to typeEqRigid *must* start with rigid types to ensure termination
typeEqRigid :: String -- String representation of the term for error reporting
            -> (Ny :* Stack Z TypeKind :* Stack Z Sem) n
            -> TypeKind -- The kind we're comparing at
            -> Val n -- Expected
            -> Val n -- Actual
            -> Checking ()
typeEqRigid tm (_ :* _ :* semz) Nat exp act = do
  -- TODO: What if there's hope in the numbers?
  exp <- sem semz exp
  act <- sem semz act
  if getNum exp == getNum act
  then pure ()
  else err $ TypeMismatch tm ("TYPEEQRIGID " ++ show exp) ("TODO " ++ show act)
typeEqRigid tm stuff@(_ :* kz :* _) (TypeFor m []) (VApp f args) (VApp f' args') | f == f' =
  svKind f >>= \case
    TypeFor m' ks | m == m' -> typeEqs tm stuff (snd <$> ks) (args <>> []) (args' <>> [])
      -- pattern should always match
    _ -> err $ InternalError "quote gave a surprising result"
 where
  svKind (VPar e) = kindOf (VPar e)
  svKind (VInx n) = pure $ proj kz n
typeEqRigid tm lvkz (TypeFor m []) (VCon c args) (VCon c' args') | c == c' =
  req (TLup (m, c)) >>= \case
        Just ks -> typeEqs tm lvkz (snd <$> ks) args args'
        Nothing -> err $ TypeErr $ "Type constructor " ++ show c
                        ++ " undefined " ++ " at kind " ++ show (TypeFor m [])
typeEqRigid tm lvkz (Star []) (VFun m0 (ins0 :->> outs0)) (VFun m1 (ins1 :->> outs1)) | Just Refl <- testEquality m0 m1 = do
  probs :: [Checking ()] <- throwLeft $ typeEqRow m0 tm lvkz ins0 ins1 >>= \case -- this is in Either ErrorMsg
        (Some (lvkz :* (Refl :* Refl)), ps1) -> typeEqRow m0 tm lvkz outs0 outs1 <&> (ps1++) . snd
  sequenceA_ probs -- uses Applicative (unlike sequence_ which uses Monad), hence parallelized
typeEqRigid tm _ _ v0 v1 = err $ TypeMismatch tm (show v0) (show v1)
