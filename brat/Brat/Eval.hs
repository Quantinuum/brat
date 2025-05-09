{-# LANGUAGE AllowAmbiguousTypes, UndecidableInstances #-}

module Brat.Eval (EvMode(..)
                 ,ValPat(..)
                 ,NumPat(..)
                 ,apply
                 ,applySem
                 ,eval
                 ,sem
                 ,semLvl
                 ,doesntOccur
                 ,evalFunTy
                 ,eqTest
                 ,getNum
                 ,kindEq
                 ,kindOf
                 ,kindType
                 ,numVal
                 ,quote
                 ,getNumVar
                 ) where

import Brat.Checker.Monad
import Brat.Checker.Types (EndType(..), kindForMode)
import Brat.Error (ErrorMsg(..))
import Brat.QualName (plain)
import Brat.Syntax.CircuitProperties (eqProps)
import Brat.Syntax.Common
import Brat.Syntax.Value
import Control.Monad.Freer (req)
import Bwd
import Hasochism
import Util (zipSameLength)

import Data.Bifunctor (second)
import Data.Functor
import Data.Kind (Type)
import Data.Type.Equality (TestEquality(..), (:~:)(..))
import Data.Foldable (traverse_)

kindType :: TypeKind -> Val Z
kindType Nat = TNat
kindType (TypeFor _ []) = VCon (plain "nil") []
kindType (TypeFor m ks)
  = VFun Braty $ helper ks :->> RPr ("type", kindType (TypeFor m [])) R0
 where
  helper :: [(PortName, TypeKind)] -> Ro Brat Z Z
  helper [] = R0
  helper ((p,k):ks) = RPr (p,kindType k) (helper ks)

-- It's very difficult to call methods from this typeclass without using type
-- applications (i.e. tyBinder @Brat) because all uses of m are arguments to type
-- families, so cannot be inferred from constraints
class MODEY m => EvMode m where
  tyBinder :: Val Z -> BinderType m
  biType :: BinderType m -> Val Z

instance EvMode Brat where
  tyBinder = Right
  biType = either kindType id

instance EvMode Kernel where
  tyBinder = id
  biType = id

numVal :: Val Z -> NumVal (VVar Z)
numVal (VApp var B0) = nVar var
numVal (VNum val) = val
numVal val = error $ "Found a " ++ show val ++ " at Nat kind"


eval :: Stack Z Sem n -> Val n -> Checking (Val Z)
eval stk v = sem stk v >>= quote Zy

evalFunTy :: Stack Z Sem n
          -> Modey m
          -> FunTy m n
          -> Checking (FunTy m Z)
evalFunTy stk my = quoteFunTy Zy my stk

sem :: Stack Z Sem n -- An environment for looking up VInxs
    -> Val n         -- The thing we're evaluating
    -> Checking Sem  -- An Inx-free value
sem ga (VNum n) = SNum <$> numEval ga n
sem ga (VCon c args) = SCon c <$> traverse (sem ga) args
sem ga (VLam body) = pure $ SLam ga body
sem ga (VFun m cty) = pure $ SFun m ga cty
sem ga (VApp f vz) = do
    f <- semVar ga f
    vz <- traverse (sem ga) vz
    applySem f vz

semVar :: Stack Z Sem n -> VVar n -> Checking Sem
semVar vz (VInx inx) = pure $ proj vz inx
semVar _ (VPar end) = req (ELup end) >>= \case
    -- v is closed, because it came from the store, but not necessarily in
    -- normal form because it could contain more defined "Par"s.
    -- (Ok to) keep going (because we don't put recursive definitions in the store).
    Just v -> sem S0 v
    Nothing -> pure $ SApp (SPar end) B0

apply :: Val Z -> [Val Z] -> Checking (Val Z)
apply f args = do
  f <- sem S0 f
  args <- traverse (sem S0) args
  res <- applySem f (B0 <>< args)
  quote Zy res

applySem :: Sem -> Bwd Sem -> Checking Sem
applySem f B0 = pure f
applySem f (vz :< v) = applySem f vz >>= \case
  SApp f vz -> pure $ SApp f (vz :< v)
  SLam ga body -> sem (ga :<< v) body
  v -> err $ InternalError $ "applySem called on " ++ show v

semLvl :: Ny n -> Sem
semLvl lvy = SApp (SLvl $ ny2int lvy) B0

-- note that typeEq is a kind of quote but that also does eta-expansion
quote :: Ny lv -> Sem -> Checking (Val lv)
quote lvy (SNum num) = pure $ VNum (fmap (quoteVar lvy) num)
quote lvy (SCon nm args) = VCon nm <$> traverse (quote lvy) args
quote lvy (SLam stk body) = do
  body <- sem (stk :<< semLvl lvy) body
  VLam <$> quote (Sy lvy) body
quote lvy (SFun my ga cty) = VFun my <$> quoteFunTy lvy my ga cty
quote lvy (SApp f vz) = VApp (quoteVar lvy f) <$> traverse (quote lvy) vz

quoteFunTy :: Ny lv -> Modey m -> Stack Z Sem n -> FunTy m n -> Checking (FunTy m lv)
quoteFunTy lvy my ga (FunTy ps ins outs) = quoteRo my ga ins lvy >>= \case
  (ga', Some (ins' :* lvy')) -> quoteRo my ga' outs lvy' >>= \case
    (_, Some (outs' :* _)) -> pure (FunTy ps ins' outs')

-- first number is next Lvl to use in Value
--         require every Lvl in Sem is < n (converted by n - 1 - lvl), else must fail at runtime
quoteVar :: Ny n -> SVar -> VVar n
quoteVar _ (SPar end) = VPar end -- no need to chase, done in semVar
quoteVar ny (SLvl lvl) = VInx $ helper ny $ ny2int ny - 1 - lvl
 where
  helper :: Ny n -> Int -> Inx n
  helper Zy _ = error "Level out of bounds"
  helper (Sy _) 0 = VZ
  helper (Sy ny) idx = VS (helper ny (idx-1))

quoteRo :: Modey m -> Stack Z Sem n -> Ro m n top -> Ny lv
          -- Some quantifies over value of (top-n)+lv
        -> Checking (Stack Z Sem top, Some (Ro m lv :* Ny))
quoteRo _ ga R0 lvy = pure (ga, Some (R0 :* lvy))
quoteRo m ga (RPr (p, t) r) lvy = do
  t <- sem ga t
  t <- quote lvy t
  (ga, Some (r :* lvy)) <- quoteRo m ga r lvy
  pure (ga, Some (RPr (p, t) r :* lvy))
quoteRo m ga (REx pk r) lvy = do
  (ga, Some (r :* lvy)) <- quoteRo m (ga :<< semLvl lvy) r (Sy lvy)
  pure (ga, Some (REx pk r :* lvy))

class NumEval (f :: Type -> Type) where
  numEval :: Stack Z Sem n -> f (VVar n) -> Checking (NumVal SVar)

instance NumEval NumVal where
  numEval ga (NumValue up grow) = nPlus up <$> numEval ga grow

instance NumEval Fun00 where
  numEval _ Constant0 = pure (nConstant 0)
  numEval ga (StrictMonoFun sm) = numEval ga sm

instance NumEval StrictMono where
  numEval l (StrictMono pow mono) = n2PowTimes pow <$> numEval l mono

instance NumEval Monotone where
  numEval ga (Linear v) = semVar ga v >>= \case
    SNum n -> pure n
    SApp sv B0 -> pure $ nVar sv
    _ -> error "Did not normalize to num or var"
  numEval ga (Full sm) = nFull <$> numEval ga sm

----------------------------------- Equality -----------------------------------
kindEq :: TypeKind -> TypeKind -> Either ErrorMsg ()
kindEq Nat Nat = Right ()
kindEq (TypeFor m xs) (TypeFor m' ys) | m == m' = kindListEq xs ys
 where
  kindListEq :: [(PortName, TypeKind)] -> [(PortName, TypeKind)] -> Either ErrorMsg ()
  kindListEq [] [] = Right ()
  kindListEq ((_, x):xs) ((_, y):ys) = kindEq x y *> kindListEq xs ys
  kindListEq _ _ = Left $ TypeErr "Unequal kind lists"
kindEq k k' = Left . TypeErr $ "Unequal kinds " ++ show k ++ " and " ++ show k'

kindOf :: VVar Z -> Checking TypeKind
kindOf (VPar e) = req (TypeOf e) >>= \case
  EndType Braty (Left k) -> pure k
  EndType my ty -> typeErr $ "End " ++ show e ++ " isn't a kind, it's type is " ++ case my of
    Braty -> show ty
    Kerny -> show ty
kindOf (VInx n) = case n of {}

-------- for SolvePatterns usage: not allowed to solve hopes,
-- and if pattern insoluble, it's not a type error (it's a "pattern match case unreachable")
eqTest :: String -- String representation of the term for error reporting
       -> TypeKind -- The kind we're comparing at
       -> Val Z -- Expected
       -> Val Z -- Actual
       -> Checking (Either ErrorMsg ())
eqTest tm k exp act = do
  exp <- sem S0 exp
  act <- sem S0 act
  eqWorker tm (Zy :* S0) k exp act

getNum :: Sem -> NumVal SVar
getNum (SApp var B0) = nVar var
getNum (SNum num) = num
getNum _ = error "Should have checked kind == Num already"

dropRight :: Either e r -> Either e ()
dropRight = second (const ())

eqWorker :: String              -- for error message
         -> (Ny :* Stack Z TypeKind) lv -- next Level & kinds for existing Levels
         -> TypeKind            -- kind of both Sem's
         -> Sem                 -- expected
         -> Sem                 -- actual
         -> Checking (Either ErrorMsg ())
eqWorker tm (lvy :* kz) (TypeFor m ((_, k):ks)) exp act = do
  -- Higher kind
  let xz = B0 :< semLvl lvy
  exp <- applySem exp xz
  act <- applySem act xz
  eqWorker tm (Sy lvy :* (kz :<< k)) (TypeFor m ks) exp act
-- Nothing else is higher kinded
eqWorker tm _ Nat exp act = pure $
  if getNum exp == getNum act then Right () else Left $
    TypeMismatch tm (show exp) (show act)
eqWorker tm (lvy :* kz) (TypeFor m []) (SApp f args) (SApp f' args') | f == f' =
  svKind (quoteVar lvy f) >>= \case
    TypeFor m' ks | m == m' -> eqTests tm (lvy :* kz) (snd <$> ks) (args <>> []) (args' <>> [])
      -- pattern should always match
    _ -> err $ InternalError "quote gave a surprising result"
 where
  svKind (VPar e) = kindOf (VPar e)
  svKind (VInx n) = pure $ proj kz n
eqWorker tm lvkz (TypeFor m []) (SCon c args) (SCon c' args') | c == c' =
  req (TLup (m, c)) >>= \case
        Just ks -> eqTests tm lvkz (snd <$> ks) args args'
        Nothing -> pure . Left . TypeErr $ "Type constructor " ++ show c
                        ++ " undefined " ++ " at kind " ++ show (TypeFor m [])
eqWorker tm lvkz (Star []) (SFun m0 stk0 (FunTy ps0 ins0 outs0)) (SFun m1 stk1 (FunTy ps1 ins1 outs1))
 -- Give nice error for kind mismatch
  | Just Refl <- testEquality m0 m1
  = if eqProps m0 ps0 ps1
    then eqRowTest m0 tm lvkz (stk0,ins0) (stk1,ins1) >>= \case
      Left msg -> pure (Left msg)
      Right (Some lvkz, stk0, stk1) -> eqRowTest m0 tm lvkz (stk0, outs0) (stk1, outs1) <&> dropRight
    -- TODO: Better error message
    else pure (Left (TypeErr "Kernels had different properties"))

eqWorker tm lvkz (TypeFor _ []) (SSum m0 stk0 rs0) (SSum m1 stk1 rs1)
  | Just Refl <- testEquality m0 m1 = case zipSameLength rs0 rs1 of
      Nothing -> pure (Left (TypeErr "Mismatched sum lengths"))
      Just rs -> traverse eqVariant rs <&> sequence_
 where
  eqVariant (Some r0, Some r1) = eqRowTest m0 tm lvkz (stk0,r0) (stk1,r1) <&> dropRight
eqWorker tm _ _ v0 v1 = pure . Left $ TypeMismatch tm (show v0) (show v1)

-- Type rows have bot0,bot1 dangling de Bruijn indices, which we instantiate with
-- de Bruijn levels. As we go under binders in these rows, we add to the scope's
-- environments, which we return at the end for eqFunType.
eqRowTest :: Modey m
          -> String -- The term we complain about in errors
          -> (Ny :* Stack Z TypeKind) lv -- Next available level, the kinds of existing levels
          -> (Stack Z Sem bot0, Ro m bot0 top0)
          -> (Stack Z Sem bot1, Ro m bot1 top1)
          -> Checking (Either ErrorMsg (Some (Ny :* Stack Z TypeKind) -- The new stack of kinds and fresh level
                                       ,Stack Z Sem top0
                                       ,Stack Z Sem top1
                                       ))
eqRowTest _ _ lvkz (stk0, R0) (stk1, R0) = pure $ Right (Some lvkz, stk0, stk1)
eqRowTest m tm lvkz (stk0, RPr (_, ty0) r0) (stk1, RPr (_, ty1) r1) = do
  let k = kindForMode m
  ty0 <- sem stk0 ty0
  ty1 <- sem stk1 ty1
  eqWorker tm lvkz k ty0 ty1 >>= \case
    Left msg -> pure $ Left msg
    Right () -> eqRowTest m tm lvkz (stk0, r0) (stk1, r1)
eqRowTest m tm (lvy :* kz) (stk0, REx (_, k0) r0) (stk1, REx (_, k1) r1) =
  case kindEq k0 k1 of
      Left msg -> pure $ Left msg
      Right () -> do
        let l = semLvl lvy
        eqRowTest m tm (Sy lvy :* (kz :<< k0)) (stk0 :<< l, r0) (stk1 :<< l, r1)
eqRowTest m tm _ exp act = modily m $ pure . Left $ TypeMismatch tm (show exp) (show act)

eqTests :: String -> (Ny :* Stack Z TypeKind) n -> [TypeKind] -> [Sem] -> [Sem] -> Checking (Either ErrorMsg ())
  -- note alternative - traverse zip3/zipSameLen*2 + currying
  -- to get [Either ErrorMsg ()], then sequenceA -> Either ErrorMsg [()]
eqTests tm lvkz = go
 where
  go [] [] [] = pure (Right ())
  go (k:ks) (u:us) (v:vs) = eqWorker tm lvkz k u v >>= \case
    Right () -> go ks us vs
    Left e -> pure $ Left e
  go _ us vs = pure . Left . TypeErr $ "Arity mismatch in type constructor arguments:\n  "
                   ++ show us ++ "\n  " ++ show vs

getNumVar :: NumVal (VVar n) -> Maybe End
getNumVar (NumValue _ (StrictMonoFun (StrictMono _ mono))) = case mono of
  Linear v -> case v of
    VPar e -> Just e
    _ -> Nothing
  Full sm -> getNumVar (numValue sm)
getNumVar _ = Nothing

-- Be conservative, fail if in doubt. Not dangerous like being wrong while succeeding
-- We can have bogus failures here because we're not normalising under lambdas
-- N.B. the value argument is normalised.
doesntOccur :: End -> Val n -> Either ErrorMsg ()
doesntOccur e (VNum nv) = traverse_ (collision e) (getNumVar nv)
doesntOccur e (VApp var args) = case var of
  VPar e' -> collision e e' *> traverse_ (doesntOccur e) args
  _ -> pure ()
doesntOccur e (VCon _ args) = traverse_ (doesntOccur e) args
doesntOccur e (VLam body) = doesntOccur e body
doesntOccur e (VFun my (FunTy _ ins outs)) = case my of
  Braty -> doesntOccurRo my e ins *> doesntOccurRo my e outs
  Kerny -> doesntOccurRo my e ins *> doesntOccurRo my e outs

collision :: End -> End -> Either ErrorMsg ()
collision e v | e == v = Left . UnificationError $
                         show e ++ " is cyclic"
              | otherwise = pure ()

doesntOccurRo :: Modey m -> End -> Ro m i j -> Either ErrorMsg ()
doesntOccurRo _ _ R0 = pure ()
doesntOccurRo my e (RPr (_, ty) ro) = doesntOccur e ty *> doesntOccurRo my e ro
doesntOccurRo Braty e (REx _ ro) = doesntOccurRo Braty e ro
