module Brat.Constructors where

import qualified Data.Map as M
import Data.Type.Equality ((:~:)(..))

import Brat.Constructors.Patterns
import Brat.QualName (QualName, plain)
import Brat.Syntax.Common
import Brat.Syntax.Value
import Bwd
import Hasochism (N(..), Ny(..), Some(..), integer2Ny, mulL)

-- TODO: Enforce the invariant that the number of pattern variables is n
data CtorArgs m where
  CArgs :: [ValPat] -- Patterns to match the arguments to Ty against
        -> Ny i        -- Number of pattern variables bound (natEqOrBust will test this)
        -> Ro Brat Z i  -- Kinds of pattern variables
        -> Ro m i j -- Inputs for the constructor node, which we should feed C's args into
        -- N.B. these can include bound variables which refer to things bound by
        -- matching the patterns in the `[ValPat]` against Ty's arguments.
        -> CtorArgs m

type ConstructorMap m
  = M.Map QualName  -- The name of a constructor "C"
    (M.Map QualName -- The name of the type we're checking against "Ty"
     (CtorArgs m)
    )

defaultConstructors :: ConstructorMap Brat
defaultConstructors = M.fromList
  [(CSucc, M.fromList
     [(CNat, CArgs [] Zy R0 (RPr ("value", TNat) R0))
     ,(CInt, CArgs [] Zy R0 (RPr ("value", TInt) R0))
     ])
  ,(CDoub, M.fromList
     [(CNat, CArgs [] Zy R0 (RPr ("value", TNat) R0))
     ,(CInt, CArgs [] Zy R0 (RPr ("value", TInt) R0))
     ])
  ,(CZero, M.fromList
     [(CNat, CArgs [] Zy R0 R0)
     ,(CInt, CArgs [] Zy R0 R0)
     ])
  ,(CNil, M.fromList
     [(CList, CArgs [VPVar] (Sy Zy) (REx ("elementType", Star []) R0) R0)
     ,(CVec, CArgs [VPVar, VPNum NP0] (Sy Zy) (REx ("elementType", Star []) R0) R0)
     ,(CNil, CArgs [] Zy R0 R0)
     ])
  ,(CCons, M.fromList
     [(CList, CArgs [VPVar] (Sy Zy)
       (REx ("elementType", Star []) R0)
       (RPr ("head", VApp (VInx VZ) B0)
         (RPr ("tail", TList (VApp (VInx VZ) B0)) R0)))
     ,(CVec, CArgs [VPVar, VPNum (NP1Plus NPVar)] (Sy (Sy Zy))
       (REx ("elementType", Star []) (REx ("tailLength", Nat) R0))
       (RPr ("head", VApp (VInx (VS VZ)) B0)
        (RPr ("tail", TVec (VApp (VInx (VS VZ)) B0) (VNum $ nVar (VInx VZ))) R0)))
     ,(CCons, CArgs [VPVar, VPCon (plain "nil") []] (Sy Zy)
       (REx ("elementType", Star []) R0)
       (RPr ("value", VApp (VInx VZ) B0) R0))
     ,(CCons, CArgs [VPVar, VPVar] (Sy (Sy Zy))
       (REx ("headTy", Star [])
        (REx ("tailTy", Star []) R0))
       (RPr ("head", VApp (VInx (VS VZ)) B0)
        (RPr ("tail", VApp (VInx VZ) B0) R0)))
     ])
  ,(CSnoc, M.fromList
     [(CList, CArgs [VPVar] (Sy Zy)
       (REx ("elementType", Star []) R0)
       (RPr ("tail", TList (VApp (VInx VZ) B0))
        (RPr ("head", VApp (VInx VZ) B0) R0)))
     ,(CVec, CArgs [VPVar, VPNum (NP1Plus NPVar)] (Sy (Sy Zy))
       (REx ("elementType", Star []) (REx ("tailLength", Nat) R0))
       (RPr ("tail", TVec (VApp (VInx (VS VZ)) B0) (VNum $ nVar (VInx VZ)))
        (RPr ("head", VApp (VInx (VS VZ)) B0) R0)))
     ])
  ,(CConcatEqEven, M.fromList
     [(CVec, CArgs [VPVar, VPNum (NP2Times NPVar)] (Sy (Sy Zy))
      -- Star should be a TypeFor m forall m?
      (REx ("elementType", Star []) (REx ("halfLength", Nat) R0))
      (RPr ("lhs", TVec (VApp (VInx (VS VZ)) B0) (VApp (VInx VZ) B0))
        (RPr ("rhs", TVec (VApp (VInx (VS VZ)) B0) (VApp (VInx VZ) B0)) R0)))
     ])
  ,(CRiffle, M.fromList
     [(CVec, CArgs [VPVar, VPNum (NP2Times NPVar)] (Sy (Sy Zy))
      -- Star should be a TypeFor m forall m?
      (REx ("elementType", Star []) (REx ("halfLength", Nat) R0))
      (RPr ("evens", TVec (VApp (VInx (VS VZ)) B0) (VApp (VInx VZ) B0))
        (RPr ("odds", TVec (VApp (VInx (VS VZ)) B0) (VApp (VInx VZ) B0)) R0)))
     ])
  ,(CConcatEqOdd, M.fromList
     [(CVec, CArgs [VPVar, VPNum (NP1Plus (NP2Times NPVar))] (Sy (Sy Zy))
      -- Star should be a TypeFor m forall m?
      (REx ("elementType", Star []) (REx ("halfLength", Nat) R0))
      (RPr ("lhs", TVec (VApp (VInx (VS VZ)) B0) (VApp (VInx VZ) B0))
        (RPr ("mid", VApp (VInx (VS VZ)) B0)
          (RPr ("rhs", TVec (VApp (VInx (VS VZ)) B0) (VApp (VInx VZ) B0)) R0))))
     ])
  ,(CNone, M.fromList
     [(COption, CArgs [VPVar] (Sy Zy) (REx ("ty", Star []) R0) R0)])
  ,(CSome, M.fromList
     [(COption, CArgs [VPVar] (Sy Zy)
        (REx ("ty", Star []) R0)
        (RPr ("value", VApp (VInx VZ) B0) R0))])
  ,(CTrue, M.fromList [(CBool, CArgs [] Zy R0 R0)])
  ,(CFalse, M.fromList [(CBool, CArgs [] Zy R0 R0)])
  ]

kernelConstructors :: ConstructorMap Kernel
kernelConstructors = M.fromList
  [(CNil, M.fromList
     [(CVec, CArgs [VPVar, VPNum NP0] (Sy Zy) (REx ("elementType", Dollar []) R0) R0)]
   )
  ,(CCons, M.fromList
     [(CVec, CArgs [VPVar, VPNum (NP1Plus NPVar)] (Sy (Sy Zy))
       (REx ("elementType", Dollar []) (REx ("tailLength", Nat) R0))
       (RPr ("head", VApp (VInx (VS VZ)) B0)
        (RPr ("tail", TVec (VApp (VInx (VS VZ)) B0) (VNum $ nVar (VInx VZ))) R0)))
     ])
  ,(CSnoc, M.fromList
     [(CVec, CArgs [VPVar, VPNum (NP1Plus NPVar)] (Sy (Sy Zy))
       (REx ("elementType", Dollar []) (REx ("tailLength", Nat) R0))
       (RPr ("tail", TVec (VApp (VInx (VS VZ)) B0) (VNum $ nVar (VInx VZ)))
        (RPr ("head", VApp (VInx (VS VZ)) B0) R0)))
     ])
  ,(CTrue, M.fromList [(CBit, CArgs [] Zy R0 R0)])
  ,(CFalse, M.fromList [(CBit, CArgs [] Zy R0 R0)])
  ]

defaultTypeConstructors :: M.Map (Mode, QualName) [(PortName, TypeKind)]
defaultTypeConstructors = M.fromList
  [((Brat, COption), [("value", Star [])])
  ,((Brat, CList),   [("listValue", Star [])])
  ,((Brat, CVec),    [("X", Star []), ("n", Nat)])
  ,((Brat, CBool),   [])
  ,((Brat, CBit),    [])
  ,((Brat, CInt),    [])
  ,((Brat, CFloat),  [])
  ,((Brat, CString), [])
  ,((Brat, CNat),    [])
  ,((Brat, CNil),    [])
  ,((Brat, CCons),   [("head", Star []), ("tail", Star [])])
  ,((Kernel, CQubit), [])
  ,((Kernel, CMoney), [])
  ,((Kernel, CVec), [("X", Dollar []), ("n", Nat)])
  ,((Kernel, CBit), [])
  ,((Kernel, CBool), [])
  ]

{-
-- TODO: Make type aliases more flexible. Allow different patterns and allow Nat
-- kinds. Allow port pulling when applying them
-- TODO: Aliases for kernel types
typeAliases :: M.Map QualName (Modey m, [ValPat], BinderType m)
typeAliases = M.empty
{- Here is an example, for `type Vec5(X) = Vec(X, n)`:
M.fromList $
  [(plain "Vec5", (Braty, [VPVar], Con (plain "Vec") (VInx VZ :|: (Simple (Num 5)))))]

-- TODO: There's no way to parse the above syntax as:
  [(plain "Vec5", (Kerny, [VPVar], Of (VInx VZ) (Simple (Num 5))))]
-}
-}

natConstructors :: M.Map QualName (Maybe NumPat, NumVal (VVar Z) -> NumVal (VVar Z))
natConstructors = M.fromList
  [(plain "succ", (Just (NP1Plus NPVar)
                  ,nPlus 1))
  ,(plain "doub", (Just (NP2Times NPVar)
                  ,n2PowTimes 1))
  ,(plain "full", (Nothing, nFull))
  ,(plain "zero", (Just NP0, id))
  ]


kernTy :: Val Z -> Some KernTy
kernTy (VCon CQubit []) = Some KTQubit
kernTy (VCon CMoney []) = Some KTMoney
kernTy (VCon CBool []) = Some KTBit
kernTy (VCon CBit []) = Some KTBit
-- Vectors with constant length
kernTy (VCon CVec [elems, VNum (NumValue size Constant0)]) = case (kernTy elems, integer2Ny size) of
         (Some elemsTy, Some sizey) -> case mul3 (ktN3y elemsTy) sizey of
            Some qmb -> Some (KTVec elemsTy sizey qmb)
kernTy _ = error "kernTy: Not of kind $"

kernRo :: Ro Kernel Z top -> (top :~: Z, Some KernTy)
kernRo R0 = (Refl, Some KTUnit)
kernRo (RPr (_, ty) ro) = case (kernTy ty, kernRo ro) of
      (Some kty, (Refl, Some kro)) -> case add3 (ktN3y kty) (ktN3y kro) of
         Some qmb -> (Refl, Some (KTPair kty kro qmb))
