module Brat.Checker.SolveHoles (typeEq) where

import Brat.Checker.Helpers (buildConst)
import Brat.Checker.Monad
import Brat.Checker.Types (kindForMode)
import Brat.Error (ErrorMsg(..))
import Brat.Eval
import Brat.Syntax.CircuitProperties (eqProps)
import Brat.Syntax.Common
import Brat.Syntax.Simple (SimpleTerm(..))
import Brat.Syntax.Value
import Control.Monad.Freer
import Bwd
import Hasochism

import Control.Monad (when)
import Data.Bifunctor (second)
import Data.Foldable (sequenceA_)
import Data.Functor
import Data.Maybe (mapMaybe)
import qualified Data.Map as M
import Data.Type.Equality (TestEquality(..), (:~:)(..))

-- Demand that two closed values are equal, we're allowed to solve variables in the
-- hope set to make this true.
-- Raises a user error if the vals cannot be made equal.
typeEq :: String -- String representation of the term for error reporting
       -> TypeKind -- The kind we're comparing at
       -> Val Z -- Expected
       -> Val Z -- Actual
       -> Checking ()
typeEq str = typeEq' str (Zy :* S0 :* S0)


-- Internal version of typeEq with environment for non-closed values
typeEq' :: String -- String representation of the term for error reporting
        -> (Ny :* Stack Z TypeKind :* Stack Z Sem) n
        -> TypeKind -- The kind we're comparing at
        -> Val n -- Expected
        -> Val n -- Actual
        -> Checking ()
typeEq' str stuff@(_ny :* _ks :* sems) k exp act = do
  hopes <- req AskHopes
  exp <- sem sems exp
  act <- sem sems act
  typeEqEta str stuff hopes k exp act

isNumVar :: Sem -> Maybe SVar
isNumVar (SNum (NumValue 0 (StrictMonoFun (StrictMono 0 (Linear v))))) = Just v
isNumVar _ = Nothing

-- Presumes that the hope set and the two `Sem`s are up to date.
typeEqEta :: String -- String representation of the term for error reporting
          -> (Ny :* Stack Z TypeKind :* Stack Z Sem) n
          -> Hopes -- A map from the hope set to corresponding FCs
          -> TypeKind -- The kind we're comparing at
          -> Sem -- Expected
          -> Sem -- Actual
          -> Checking ()
typeEqEta tm (lvy :* kz :* sems) hopes (TypeFor m ((_, k):ks)) exp act = do
  -- Higher kinded things
  let nextSem = semLvl lvy
  let xz = B0 :< nextSem
  exp <- applySem exp xz
  act <- applySem act xz
  typeEqEta tm (Sy lvy :* (kz :<< k) :* (sems :<< nextSem)) hopes (TypeFor m ks) exp act
-- Not higher kinded - check for flex terms
-- (We don't solve under binders for now, so we only consider Zy here)
-- 1. "easy" flex cases
typeEqEta _tm (Zy :* _ks :* _sems) hopes k (SApp (SPar (InEnd e)) B0) act
  | M.member e hopes = solveHope k e act
typeEqEta _tm (Zy :* _ks :* _sems) hopes k exp (SApp (SPar (InEnd e)) B0)
  | M.member e hopes = solveHope k e exp
typeEqEta _ (Zy :* _ :* _) hopes Nat exp act
  | Just (SPar (InEnd e)) <- isNumVar exp, M.member e hopes = solveHope Nat e act
  | Just (SPar (InEnd e)) <- isNumVar act, M.member e hopes = solveHope Nat e exp
-- 2. harder cases, neither is in the hope set, so we can't define it ourselves
typeEqEta tm stuff@(ny :* _ks :* _sems) hopes k exp act = do
  exp <- quote ny exp
  act <- quote ny act
  let ends = mapMaybe getEnd [exp,act]
  -- sanity check: we've already dealt with either end being in the hopeset
  when (or [M.member ie hopes | InEnd ie <- ends]) $ typeErr "ends were in hopeset"
  case ends of
    [] -> typeEqRigid tm stuff k exp act -- easyish, both rigid i.e. already defined
    -- variables are trivially the same, even if undefined, but the values may
    -- be different! E.g. X =? 1 + X
    [_, _] | exp == act -> pure ()
    -- TODO: Once we have scheduling, we must wait for one or the other to become more defined, rather than failing
    _  -> err (TypeMismatch tm (show exp) (show act))
 where
  getEnd (VApp (VPar e) _) = Just e
  getEnd (VNum n) = getNumVar n
  getEnd _ = Nothing

-- This will update the `hopes`, potentially invalidating things that have
-- been eval'd.
-- The Sem is closed, for now.
solveHope :: TypeKind -> InPort -> Sem -> Checking ()
solveHope k hope v = quote Zy v >>= \v -> case doesntOccur (InEnd hope) v of
  Right () -> do
    defineEnd (InEnd hope) v
    dangling <- case (k, v) of
      (Nat, VNum _v) -> err $ Unimplemented "Nat hope solving" []
      (Nat, _) -> err $ InternalError "Head of Nat wasn't a VNum"
      _ -> buildConst Unit TUnit
    req (Wire (end dangling, kindType k, hope))
    req (RemoveHope hope)
  Left msg -> case v of
    VApp (VPar (InEnd end)) B0 | hope == end -> pure ()
    -- TODO: Not all occurrences are toxic. The end could be in an argument
    -- to a hoping variable which isn't used.
    -- E.g. h1 = h2 h1 - this is valid if h2 is the identity, or ignores h1.
    _ -> err msg

typeEqs :: String -> (Ny :* Stack Z TypeKind :* Stack Z Sem) n -> [TypeKind] -> [Val n] -> [Val n] -> Checking ()
typeEqs _ _ [] [] [] = pure ()
typeEqs tm stuff (k:ks) (exp:exps) (act:acts) = typeEqs tm stuff ks exps acts <* typeEq' tm stuff k exp act
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
  else err $ TypeMismatch tm (show exp) (show act)
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
typeEqRigid tm lvkz (Star []) (VFun m0 (FunTy ps0 ins0 outs0)) (VFun m1 (FunTy ps1 ins1 outs1))
 | Just Refl <- testEquality m0 m1
 , eqProps m0 ps0 ps1 = do
  probs :: [Checking ()] <- throwLeft $ typeEqRow m0 tm lvkz ins0 ins1 >>= \case -- this is in Either ErrorMsg
        (Some (lvkz :* (Refl :* Refl)), ps1) -> typeEqRow m0 tm lvkz outs0 outs1 <&> (ps1++) . snd
  sequenceA_ probs -- uses Applicative (unlike sequence_ which uses Monad), hence parallelized
typeEqRigid tm _ _ v0 v1 = err $ TypeMismatch tm (show v0) (show v1)
