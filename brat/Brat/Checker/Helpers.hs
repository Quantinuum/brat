{-# LANGUAGE AllowAmbiguousTypes #-}

module Brat.Checker.Helpers where

import Brat.Checker.Monad (Checking, CheckingSig(..), captureOuterLocals, err, typeErr, kindArgRows, defineEnd, tlup, isSkolem, mkYield, throwLeft)
import Brat.Checker.Types
import Brat.Error (ErrorMsg(..))
import Brat.Eval (eval, EvMode(..), kindType, quote, doesntOccur)
import Brat.FC (FC)
import Brat.Graph (Node(..), NodeType(..))
import Brat.Naming (FreshMonad(..), Name(..))
import Brat.Syntax.Common
import Brat.Syntax.Core (Term(..))
import Brat.Syntax.Simple
import Brat.Syntax.Port (ToEnd(..), endName)
import Brat.Syntax.Value
import Bwd
import Hasochism
import Util (log2)

import Control.Monad ((>=>))
import Control.Monad.Freer
import Control.Monad.State.Lazy (StateT(..), runStateT)
import Data.Bifunctor
import Data.Foldable (foldrM)
import Data.List (partition)
import Data.Maybe (isJust)
import Data.Type.Equality (TestEquality(..), (:~:)(..))
import qualified Data.Set as S
import Prelude hiding (last)

import Debug.Trace

trackPermission = const id
--trackPermission = trace

simpleCheck :: Modey m -> Val Z -> SimpleTerm -> Checking ()
simpleCheck my ty tm = case (my, ty) of
  (Braty, VApp (VPar e) _) -> do
    mine <- mineToSolve
    if isJust (mine e) then
      case tm of
        Float _ -> defineEnd "simpleCheck" e TFloat
        Text _ -> defineEnd "simpleCheck" e TText
        Num n | n < 0 -> defineEnd "simpleCheck" e TInt
        Num _ -> typeErr $ "Can't determine whether Int or Nat: " ++ show tm
    else isSkolem e >>= \case
      SkolemConst -> throwLeft $ helper Braty ty tm
      Definable -> do
        mkYield "simpleCheck" (S.singleton e)
        ty <- eval S0 ty
        simpleCheck Braty ty tm
  _ -> throwLeft $ helper my ty tm
 where
  helper :: Modey m -> Val Z -> SimpleTerm -> Either ErrorMsg ()
  helper Braty TNat (Num n) | n >= 0 = pure ()
  helper Braty TInt (Num _) = pure ()
  helper Braty TFloat (Float _) = pure ()
  helper Braty TText (Text _) = pure ()
  helper _ ty tm = Left $ TypeErr $ unwords
                      ["Expected something of type"
                      ,"`" ++ show ty ++ "`"
                      ,"but got"
                      ,"`" ++ show tm ++ "`"
                      ]

-- Port pulling, but with no moving of/around binders (TODO)
pull1PortRo :: MODEY m
            => Modey m
            -> PortName -- The port we want to pull to the front
            -> Bwd (PortName, Val bot) -- The things we've passed so far
            -> Ro m bot top -- The row we've got left to traverse
            -> Checking ((PortName, Val bot), Ro m bot top)
-- TODO: Make an `Error` constructor for this
pull1PortRo _ p _ R0 = fail $ "Port not found: " ++ p
pull1PortRo m p stuff (RPr (p', ty) ro)
 | p == p' = if portNameExists m p ro
   then err (AmbiguousPortPull p (show (RPr (p', ty) ro)))
   else pure ((p', ty), rebuildRo m ro (stuff <>> []))
 | otherwise = pull1PortRo m p (stuff :< (p', ty)) ro
 where
  rebuildRo :: Modey m
            -> Ro m bot top -- The row that we still haven't traversed
            -> [(PortName, Val bot)] -- The stuff we've passed
            -> Ro m bot top
  rebuildRo _ ro [] = ro
  rebuildRo m ro (x:xs) = RPr x (rebuildRo m ro xs)

  portNameExists :: Modey m -> PortName -> Ro m bot top -> Bool
  portNameExists _ _ R0 = False
  portNameExists m p (RPr (p', _) ro)
   | p == p' = True
   | otherwise = portNameExists m p ro
  portNameExists Braty p (REx (p', _) ro)
   | p == p' = True
   | otherwise = portNameExists Braty p ro
-- TODO: Make an `Error` for this
-- TODO: Enable this later
pull1PortRo Braty _ _ (REx _ _) = fail "Port pull past a type binder"

pullPortsRo :: MODEY m => Modey m -> [PortName] -> Ro m bot top -> Checking (Ro m bot top)
pullPortsRo _ [] ro = pure ro
pullPortsRo m (p:ps) ro = do
  (x, ro) <- pull1PortRo m p B0 ro
  RPr x <$> pullPortsRo m ps ro

pullPortsRow :: Show ty
             => [PortName]
             -> [(NamedPort e, ty)]
             -> Checking [(NamedPort e, ty)]
pullPortsRow = pullPorts (portName . fst) showRow

pullPortsSig :: Show ty
             => [PortName]
             -> [(PortName, ty)]
             -> Checking [(PortName, ty)]
pullPortsSig = pullPorts fst showSig

pullPorts :: forall a
           . (a -> PortName) -- A way to get a port name for each element
          -> ([a] -> String) -- A way to print the list
          -> [PortName] -- Things to pull to the front
          -> [a]  -- The list to rearrange
          -> Checking [a]
pullPorts toPort showFn to_pull types =
  -- the "state" here is the things still available to be pulled
  uncurry (++) <$> runStateT (mapM pull1Port to_pull) types
 where
  pull1Port :: PortName -> StateT [a] Checking a
  pull1Port p = StateT $ \available -> case partition ((== p) . toPort) available of
      ([], _) -> err $ BadPortPull p (showFn available)
      ([found], remaining) -> pure (found, remaining)
      (_, _) -> err $ AmbiguousPortPull p (showFn available)

ensureEmpty :: Show ty => String -> [(NamedPort e, ty)] -> Checking ()
ensureEmpty _ [] = pure ()
ensureEmpty str xs = err $ InternalError $ "Expected empty " ++ str ++ ", got:\n  " ++ showSig (rowToSig xs)

rowToSig :: Traversable t => t (NamedPort e, ty) -> t (PortName, ty)
rowToSig = fmap $ first portName

showMode :: Modey m -> String
showMode Braty = ""
showMode Kerny = "(kernel) "

type family ThunkFCType (m :: Mode) where
  ThunkFCType Brat = FC
  ThunkFCType Kernel = ()

type family ThunkRowType (m :: Mode) where
  ThunkRowType Brat = KindOr (Term Chk Noun)
  ThunkRowType Kernel = Term Chk Noun

mkThunkTy :: Modey m
          -> ThunkFCType m
          -> [(PortName, ThunkRowType m)]
          -> [(PortName, ThunkRowType m)]
          -> Term Chk Noun
-- mkThunkTy Braty fc ss ts = C (WC fc (ss :-> ts))
mkThunkTy Braty _ ss ts = C (ss :-> ts)
mkThunkTy Kerny () ss ts = K (ss :-> ts)

anext :: forall m i j k
       . EvMode m
      => String
      -> NodeType m
      -> (Semz i, Some Endz)
      -> Ro m i j -- Inputs and Outputs use de Bruijn indices
      -> Ro m j k
      -> Checking (Name, Unders m Chk, Overs m UVerb, (Semz k, Some Endz))
anext str th vals0 ins outs = anext' str th vals0 ins outs $ case th of
  Source -> SkolemConst
  _ -> Definable

anext' :: forall m i j k
       . EvMode m
      => String
      -> NodeType m
      -> (Semz i, Some Endz)
      -> Ro m i j -- Inputs and Outputs use de Bruijn indices
      -> Ro m j k
      -> IsSkolem -- inports are always Definable
      -> Checking (Name, Unders m Chk, Overs m UVerb, (Semz k, Some Endz))
anext' str th vals0 ins outs skol = do
  node <- req (Fresh str) -- Pick a name for the thunk
  -- Use the new name to generate Ends with which to instantiate types
  (unders, vals1) <- endPorts node InEnd In 0 vals0 ins
  (overs, vals2)  <- endPorts node ExEnd Ex 0 vals1 outs
  () <- sequence_ $
        [ declareTgt tgt (modey @m) ty | (tgt, ty) <- unders ] ++
        [ req (Declare (ExEnd (end src)) (modey @m) ty skol) | (src, ty) <- overs ]

  let inputs  = [ (portName p, biType @m ty) | (p, ty) <- unders ]
  let outputs = [ (portName p, biType @m ty) | (p, ty) <- overs  ]

  () <- req (AddNode node (mkNode (modey @m) th inputs outputs))
  pure (node, unders, overs, vals2)

mkNode :: forall m. Modey m -> NodeType m
        -> [(PortName, Val Z)]
        -> [(PortName, Val Z)]
        -> Node
mkNode Braty = BratNode
mkNode Kerny = KernelNode

type Endz = Ny :* Stack Z End

-- endPorts instantiates the de Bruijn variables in a row with Ends
endPorts :: forall m i j port
          . EvMode m
         => Name -> (port -> End) -> (Name -> Int -> port)
         -> Int -- Next free port on the node
         -> (Semz i, Some Endz)
         -> Ro m i j
         -> Checking ([(NamedPort port, BinderType m)], (Semz j, Some Endz))
endPorts _ _ _ _ stuff R0 = pure ([], stuff)
endPorts node port2End mkPort n (ga, ez) (RPr (p,ty) ro) = do
  ty <- eval ga ty
  (row, stuff) <- endPorts node port2End mkPort (n + 1) (ga, ez) ro
  pure ((NamedPort (mkPort node n) p, tyBinder @m ty):row, stuff)
endPorts node port2End mkPort n (ga, Some (ny :* endz)) (REx (p, k) ro) = do
  let port = mkPort node n
  let end = port2End port
  (row, stuff) <- endPorts node port2End mkPort (n + 1)
                  (ga :<< SApp (SPar end) B0, Some (Sy ny :* (endz :<< end))) ro
  pure ((NamedPort port p, Left k):row, stuff)
next :: String -> NodeType Brat -> (Semz i, Some Endz)
     -> Ro Brat i j
     -> Ro Brat j k
     -> Checking (Name, Unders Brat Chk, Overs Brat UVerb, (Semz k, Some Endz))
next = let ?my = Braty in anext

knext :: String -> NodeType Kernel -> (Semz i, Some Endz)
      -> Ro Kernel i i
      -> Ro Kernel i i
      -> Checking (Name, Unders Kernel Chk, Overs Kernel UVerb, (Semz i, Some Endz))
knext = let ?my = Kerny in anext

wire :: (Src, Val Z, Tgt) -> Checking ()
wire (src, ty, tgt) = do
  ty <- eval S0 ty
  req $ Wire (end src, ty, end tgt)

-- Called by check when synthesising a function.
-- Given a row of overs which starts with some function types for the same mode:
--   * Create an eval node for each function
--   * Compute the combined overs/unders for the juxtaposition of those evals
--     (because we want to support application of juxtaposed functions)
--   * Return the eval nodes and the combined overs/unders
--
-- The functions in the overs should be Inx-closed
--
-- Unders and Overs here are respectively the inputs and outputs for the thunks
-- This is the dual notion to the overs and unders used for typechecking against
-- Hence, we return them here in the opposite order to `check`'s connectors
getThunks :: Modey m
          -> [(Src, BinderType Brat)] -- A row of 0 or more function types in the same mode
          -> Checking ([Name]
                      ,Unders m Chk
                      ,Overs m UVerb
                      )
getThunks _ [] = pure ([], [], [])
getThunks Braty ((src, Right ty):rest) = do
  ty <- awaitTypeDefinition ty
  (src, ss :->> ts) <- vectorise Braty (src, ty)
  (node, unders, overs, _) <- let ?my = Braty in
                                anext "Eval" (Eval (end src)) (S0, Some (Zy :* S0)) ss ts
  (nodes, unders', overs') <- getThunks Braty rest
  pure (node:nodes, unders <> unders', overs <> overs')
getThunks Kerny ((src, Right ty):rest) = do
  ty <- awaitTypeDefinition ty
  (src, ss :->> ts) <- vectorise Kerny (src,ty)
  (node, unders, overs, _) <- let ?my = Kerny in anext "Splice" (Splice (end src)) (S0, Some (Zy :* S0)) ss ts
  (nodes, unders', overs') <- getThunks Kerny rest
  pure (node:nodes, unders <> unders', overs <> overs')
getThunks Braty ((src, Left (Star args)):rest) = do
  (node, unders, overs) <- case bwdStack (B0 <>< args) of
    Some (_ :* stk) -> do
      let (ri,ro) = kindArgRows stk
      (node, unders, overs, _) <- next "Eval" (Eval (end src)) (S0, Some (Zy :* S0)) ri ro
      pure (node, unders, overs)
  (nodes, unders', overs') <- getThunks Braty rest
  pure (node:nodes, unders <> unders', overs <> overs')
getThunks m ro = err $ ExpectedThunk (showMode m) (showRow ro)

-- The type given here should be normalised
vecLayers :: Modey m -> Val Z -> Checking ([(Src, NumVal (VVar Z))] -- The sizes of the vector layers
                                          ,CTy m Z -- The function type at the end
                                          )
vecLayers my (TVec ty (VNum n)) = do
  src <- buildNatVal n
  first ((src, n):) <$> vecLayers my ty
vecLayers Braty (VFun Braty cty) = pure ([], cty)
vecLayers Kerny (VFun Kerny cty) = pure ([], cty)
vecLayers my ty = typeErr $ "Expected a " ++ showMode my ++ "function or vector of functions, got " ++ show ty

vectorise :: forall m. Modey m -> (Src, Val Z) -> Checking (Src, CTy m Z)
vectorise my (src, ty) = do
  (layers, cty) <- vecLayers my ty
  modily my $ foldrM mkMapFun (src, cty) layers
 where
  mkMapFun :: (Src, NumVal (VVar Z)) -- Layer to apply
            -> (Src, CTy m Z) -- The input to this level of mapfun
            -> Checking (Src, CTy m Z)
  mkMapFun (lenSrc, len) (valSrc, cty) = do
    let weak1 = changeVar (Thinning (ThDrop ThNull))
    vecFun <- vectorisedFun len my cty
    (_, [(lenTgt,_), (valTgt, _)], [(vectorSrc, Right (VFun my' cty))], _) <-
      next "MapFun" MapFun (S0, Some (Zy :* S0))
      (REx ("len", Nat) (RPr ("value", weak1 ty) R0))
      (RPr ("vector", weak1 vecFun) R0)
    defineTgt' "vectorise" lenTgt (VNum len)
    wire (lenSrc, kindType Nat, lenTgt)
    wire (valSrc, ty, valTgt)
    let vecCTy = case (my,my',cty) of
          (Braty,Braty,cty) -> cty
          (Kerny,Kerny,cty) -> cty
          _ -> error "next returned wrong mode of computation type to that passed in"
    pure (vectorSrc, vecCTy)

  vectorisedFun :: NumVal (VVar Z) -> Modey m -> CTy m Z -> Checking (Val Z)
  vectorisedFun nv my (ss :->> ts) = do
    (ss', ny) <- vectoriseRo True nv Zy ss
    (ts', _)  <- vectoriseRo False nv ny ts
    pure $ modily my $ VFun my (ss' :->> ts')

  -- We don't allow existentials in vectorised functions, so the boolean says
  -- whether we are in the input row and can allow binding
  vectoriseRo :: Bool -> NumVal (VVar Z) -> Ny i -> Ro m i j -> Checking (Ro m i j, Ny j)
  vectoriseRo _ _ ny R0 = pure (R0, ny)
  vectoriseRo True n ny (REx k ro) = do (ro', ny') <- vectoriseRo True n (Sy ny) ro
                                        pure (REx k ro', ny')
  vectoriseRo False _ _ (REx _ _) =
    typeErr "Type variable binding not allowed in the output type of a vectorised function"
  vectoriseRo b n ny (RPr (p, ty) ro) = do
    (ro', ny') <- vectoriseRo b n ny ro
    pure (RPr (p, TVec ty (VNum (changeVar (Thinning (thEmpty ny)) <$> n))) ro', ny')

binderToValue :: Modey m -> BinderType m -> Val Z
binderToValue Braty (Left k) = kindType k
binderToValue Braty (Right ty) = ty
binderToValue Kerny v = v

valueToBinder :: Modey m -> Val Z -> BinderType m
valueToBinder Braty = Right
valueToBinder Kerny = id

defineSrc :: Src -> Val Z -> Checking ()
defineSrc src = defineEnd "" (ExEnd (end src))

-- TODO: Do the work of checking if there's a dynamic hope here
defineTgt :: Tgt -> Val Z -> Checking ()
defineTgt tgt = defineEnd "" (InEnd (end tgt))

defineSrc' :: String -> Src -> Val Z -> Checking ()
defineSrc' lbl src = defineEnd lbl (ExEnd (end src))

defineTgt' :: String -> Tgt -> Val Z -> Checking ()
defineTgt' lbl tgt = defineEnd lbl (InEnd (end tgt))

declareTgt :: Tgt -> Modey m -> BinderType m -> Checking ()
declareTgt tgt my ty = req (Declare (InEnd (end tgt)) my ty Definable)

-- listToRow :: [(PortName, BinderType m)] -> Ro m Z i
-- listToRow [] = R0
-- listToRow ((

-- Build a box corresponding to the inside of a thunk
makeBox :: (?my :: Modey m, EvMode m)
        => String -- A label for the nodes we create
        -> CTy m Z
        -> ((Overs m UVerb, Unders m Chk) -> Checking a) -- checks + builds the body using srcs/tgts from the box
        -> Checking ((Src, BinderType Brat), a)
makeBox name cty@(ss :->> ts) body = do
  (src, _, overs, ctx) <- anext (name ++ "/in") Source (S0, Some (Zy :* S0)) R0 ss
  (tgt, unders, _, _) <- anext (name ++ "/out") Target ctx ts R0
  case (?my, body) of
    (Kerny, _) -> do
      (_,_,[thunk],_) <- next (name ++ "_thunk") (Box src tgt) (S0, Some (Zy :* S0))
                                R0 (RPr ("thunk", VFun Kerny cty) R0)
      bres <- body (overs, unders)
      pure (thunk, bres)
    (Braty, body) -> do
      (node, [], [thunk], _) <- next (name ++ "_thunk") (Box src tgt) (S0, Some (Zy :* S0))
                                     R0 (RPr ("thunk", VFun ?my cty) R0)
      bres <- captureOuterLocals node (body (overs, unders))
      pure (thunk, bres)

-- Evaluate either mode's BinderType
evalBinder :: Modey m -> BinderType m -> Checking (BinderType m)
evalBinder Kerny sty = eval S0 sty
evalBinder Braty (Right ty) = Right <$> eval S0 ty
evalBinder Braty (Left k) = pure (Left k)

-- If this goes wrong, we probably messed up writing the constructor table
natEqOrBust :: Ny i -> Ny j -> Either ErrorMsg (i :~: j)
natEqOrBust n m | Just q <- testEquality n m = pure q
natEqOrBust _ _ = Left $ InternalError "We can't count"

rowToRo :: ToEnd t => Modey m -> [(String, t, BinderType m)] -> Stack Z End i -> Checking (Some (Ro m i :* Stack Z End))
rowToRo _ [] stk = pure $ Some (R0 :* stk)
rowToRo Kerny ((p, _, ty):row) S0 = do
  ty <- eval S0 ty
  rowToRo Kerny row S0 >>= \case
    Some (ro :* stk) -> pure . Some $ RPr (p, changeVar (ParToInx (AddZ Zy) S0) ty) ro :* stk
rowToRo Kerny _ (_ :<< _) = err $ InternalError "rowToRo - no binding allowed in kernels"

rowToRo Braty ((p, _, Right ty):row) endz = do
  ty <- eval S0 ty
  rowToRo Braty row endz >>= \case
    Some (ro :* stk) -> pure . Some $ RPr (p, changeVar (ParToInx (AddZ (stackLen endz)) endz) ty) ro :* stk
rowToRo Braty ((p, tgt, Left k):row) endz = rowToRo Braty row (endz :<< toEnd tgt) >>= \case
  Some (ro :* stk) -> pure . Some $ REx (p, k) ro :* stk

roToTuple :: Ro m Z Z -> Val Z
roToTuple R0 = TNil
roToTuple (RPr (_, ty) ro) = TCons ty (roToTuple ro)
roToTuple (REx _ _) = error "the impossible happened"

-- Low hanging fruit that we can easily do to our normal forms of numbers
runArith :: NumVal (VVar Z) -> ArithOp -> NumVal (VVar Z) -> Maybe (NumVal (VVar Z))
runArith (NumValue upl grol) Add (NumValue upr gror)
-- We can add when one of the sides is a constant...
 | Constant0 <- grol = pure $ NumValue (upl + upr) gror
 | Constant0 <- gror = pure $ NumValue (upl + upr) grol
 -- ... or when Fun00s are the same
 | grol == gror = pure $ NumValue (upl + upr) grol
runArith (NumValue upl grol) Sub (NumValue upr gror)
-- We can subtract when the rhs is a constant...
 | Constant0 <- gror, upl >= upr = pure $ NumValue (upl - upr) grol
 -- ... or when the Fun00s are the same...
 | grol == gror, upl >= upr = pure $ NumValue (upl - upr) Constant0
 -- ... or we have (c + 2^(k + 1) * x) - (c' + 2^k * x)
 | StrictMonoFun (StrictMono k m) <- grol
 , StrictMonoFun (StrictMono k' m') <- gror
 , m == m'
 , k == (k' + 1)
 , upl >= upr = pure $ NumValue (upl - upr) gror
runArith (NumValue upl grol) Mul (NumValue upr gror)
 -- We can multiply two constants...
 | Constant0 <- grol
 , Constant0 <- gror = pure $ NumValue (upl * upr) grol
 -- ... or we can multiply by a power of 2
 | Constant0 <- grol
 , StrictMonoFun (StrictMono k' m) <- gror
 , Just k <- log2 upl = pure $ NumValue (upl * upr) (StrictMonoFun (StrictMono (k + k') m))
 | Constant0 <- gror
 , StrictMonoFun (StrictMono k' m) <- grol
 , Just k <- log2 upr = pure $ NumValue (upl * upr) (StrictMonoFun (StrictMono (k + k') m))
runArith (NumValue upl grol) Pow (NumValue upr gror)
 -- We can take constants to the power of constants...
 | Constant0 <- grol
 , Constant0 <- gror = pure $ NumValue (upl ^ upr) Constant0
 -- ... or we can take a constant to the power of a NumValue if the constant
 -- is 2^(2^c)
 | Constant0 <- grol
 , Just l <- log2 upl
 , Just k <- log2 l
 , StrictMonoFun (StrictMono k' mono) <- gror
 -- 2^(2^k) ^ (upr + (2^k' * mono))
 -- (2^(2^k))^upr * (2^(2^k))^(2^k' * mono)
 -- 2^(2^k * upr) * 2^(2^k * (2^k' * mono))
 -- 2^(2^k * upr) * (1 + 2^(2^k * (2^k' * mono)) - 1)
 -- 2^(2^k * upr) + 2^(2^k * upr) * (2^(2^k * (2^k' * mono)) - 1)
 -- 2^(2^k * upr) + 2^(2^k * upr) * (full(2^k * (2^k' * mono))
 -- 2^(2^k * upr) + 2^(2^k * upr) * (full(2^(k + k') * mono))
 = pure $ NumValue (upl ^ upr) (StrictMonoFun (StrictMono (l * upr) (Full (StrictMono (k + k') mono))))
runArith _ _ _ = Nothing

buildArithOp :: ArithOp -> Checking ((Tgt, Tgt), Src)
buildArithOp op = do
  (_, [(lhs,_), (rhs,_)], [(out,_)], _) <- next (show op) (ArithNode op) (S0, Some (Zy :* S0)) (RPr ("lhs", TNat) (RPr ("rhs", TNat) R0)) (RPr ("value", TNat) R0)
  pure ((lhs, rhs), out)

buildConst :: SimpleTerm -> Val Z -> Checking Src
buildConst tm ty = do
  (_, _, [(out,_)], _) <- next "buildConst" (Const tm) (S0, Some (Zy :* S0)) R0 (RPr ("value", ty) R0)
  pure out

buildNum :: Integer -> Checking Src
buildNum n = buildConst (Num (fromIntegral n)) TNat

buildAdd :: Integer -> Checking (Tgt, Src)
buildAdd n = do
  nDangling <- buildNum n
  ((lhs,rhs),out) <- buildArithOp Add
  req $ Wire (end nDangling, TNat, end lhs)
  defineSrc out (VNum (nPlus n (nVar (VPar (toEnd rhs)))))
  pure (rhs, out)

buildSub :: Integer -> Checking (Tgt, Src)
buildSub n = do
  nDangling <- buildNum n
  ((lhs,rhs),out) <- buildArithOp Sub
  req $ Wire (end nDangling, TNat, end rhs)
  defineTgt' "Sub" lhs (VNum (nPlus n (nVar (VPar (toEnd out)))))
  pure (lhs, out)

buildDoub :: Checking (Tgt, Src)
buildDoub = do
  nDangling <- buildNum 2
  ((lhs,rhs),out) <- buildArithOp Mul
  req $ Wire (end nDangling, TNat, end lhs)
  defineSrc out (VNum (n2PowTimes 1 (nVar (VPar (toEnd rhs)))))
  pure (rhs, out)

buildHalve :: Checking (Tgt, Src)
buildHalve = do
  nDangling <- buildNum 2
  ((lhs,rhs),out) <- buildArithOp Div
  req $ Wire (end nDangling, TNat, end rhs)
  defineTgt' "Helpers"lhs (VNum (n2PowTimes 1 (nVar (VPar (toEnd out)))))
  pure (lhs, out)

-- Return an End with the same polarity whose value is half that of the input End
makeHalf :: End -> Checking End
makeHalf (InEnd e) = do
  (doubIn, doubOut) <- buildDoub
  req (Wire (end doubOut, TNat, e))
  defineTgt' "Helpers"(NamedPort e "") (VNum (nVar (VPar (toEnd doubOut))))
  pure (InEnd (end doubIn))
makeHalf (ExEnd e) = do
  (halveIn, halveOut) <- buildHalve
  req (Wire (e, TNat, end halveIn))
  defineSrc (NamedPort e "") (VNum (nVar (VPar (toEnd halveIn))))
  pure (toEnd halveOut)

makePred :: End -> Checking End
makePred (InEnd e) = do
  (succIn, succOut) <- buildAdd 1
  req (Wire (end succOut, TNat, e))
  defineTgt' "Helpers"(NamedPort e "") (VNum (nVar (VPar (toEnd succOut))))
  pure (toEnd succIn)
makePred (ExEnd e) = do
  (predIn, predOut) <- buildSub 1
  req (Wire (e, TNat, end predIn))
  defineSrc (NamedPort e "") (VNum (nVar (VPar (toEnd predIn))))
  pure (toEnd predOut)

-- Generate wiring to produce a dynamic instance of the numval argument
-- N.B. In these functions, we wire using Req, rather than the `wire` function
-- because we don't want it to do any extra evaluation.
buildNatVal :: NumVal (VVar Z) -> Checking Src
buildNatVal nv@(NumValue n gro) = case n of
  0 -> buildGro gro
  n -> do
    (inn, out) <- buildAdd n
    src <- buildGro gro
    req $ Wire (end src, TNat, end inn)
    --traceM $ "buildNatVal " ++ show inn
    defineTgt' "Helpers"inn (VNum (nVar (VPar (toEnd src))))
    pure out
 where
  buildGro :: Fun00 (VVar Z) -> Checking Src
  buildGro Constant0 = buildNum 0
  buildGro (StrictMonoFun sm) = buildSM sm

  buildSM :: StrictMono (VVar Z) -> Checking Src
  buildSM (StrictMono k mono) = do
    factor <- buildNum $ 2 ^ k
    -- Multiply mono by 2^k; note we could avoid this if k==0
    ((lhs,rhs),out) <- buildArithOp Mul
    monoDangling <- buildMono mono
    req $ Wire (end factor, TNat, end lhs)
    req $ Wire (end monoDangling, TNat, end rhs)
    defineSrc out (VNum (n2PowTimes k (nVar (VPar (toEnd monoDangling)))))
    pure out

  buildMono :: Monotone (VVar Z) -> Checking Src
  buildMono (Linear (VPar (ExEnd e))) = pure $ NamedPort e "numval"
  buildMono (Full sm) = do
    -- Calculate 2^n as `outPlus1`
    two <- buildNum 2
    dangling <- buildSM sm
    ((lhs,rhs),outPlus1) <- buildArithOp Pow
    req $ Wire (end two, TNat, end lhs)
    req $ Wire (end dangling, TNat, end rhs)
    -- Then subtract 1
    one <- buildNum 1
    ((lhs,rhs),out) <- buildArithOp Sub
    req $ Wire (end outPlus1, TNat, end lhs)
    req $ Wire (end one, TNat, end rhs)
    defineSrc out (VNum (nFull (nVar (VPar (toEnd dangling)))))
    pure out
  buildMono _ = err . InternalError $ "Trying to build a non-closed nat value: " ++ show nv

invertNatVal :: NumVal (VVar Z) -> Checking Tgt
invertNatVal (NumValue up gro) = case up of
  0 -> invertGro gro
  _ -> do
    ((lhs,rhs),out) <- buildArithOp Sub
    upSrc <- buildNum up
    req $ Wire (end upSrc, TNat, end rhs)
    tgt <- invertGro gro
    req $ Wire (end out, TNat, end tgt)
    defineTgt' "Helpers"tgt (VNum (nVar (VPar (toEnd out))))
    defineTgt' "Helpers"lhs (VNum (nPlus up (nVar (VPar (toEnd tgt)))))
    pure lhs
 where
  invertGro Constant0 = error "Invariant violated: the numval arg to invertNatVal should contain a variable"
  invertGro (StrictMonoFun sm) = invertSM sm

  invertSM (StrictMono k mono) = case k of
    0 -> invertMono mono
    _ -> do
      divisor <- buildNum (2 ^ k)
      ((lhs,rhs),out) <- buildArithOp Div
      tgt <- invertMono mono
      req $ Wire (end out, TNat, end tgt)
      req $ Wire (end divisor, TNat, end rhs)
      defineTgt' "Helpers"tgt (VNum (nVar (VPar (toEnd out))))
      defineTgt' "Helpers"lhs (VNum (n2PowTimes k (nVar (VPar (toEnd tgt)))))
      pure lhs

  invertMono (Linear (VPar (InEnd e))) = pure (NamedPort e "numval")
  invertMono (Full sm) = do
    (_, [(llufTgt,_)], [(llufSrc,_)], _) <- next "luff" (Prim ("BRAT","lluf")) (S0, Some (Zy :* S0)) (REx ("n", Nat) R0) (REx ("n", Nat) R0)
    tgt <- invertSM sm
    req $ Wire (end llufSrc, TNat, end tgt)
    defineTgt' "Helpers"tgt (VNum (nVar (VPar (toEnd llufSrc))))
    defineTgt' "Helpers"llufTgt (VNum (nFull (nVar (VPar (toEnd tgt)))))
    pure llufTgt

-- This will update the `hopes`, potentially invalidating things that have
-- been eval'd.
-- The Sem is closed, for now.
solveVal :: TypeKind -> End -> Val Z -> Checking ()
solveVal _ it (VApp (VPar e) B0) | it == e = pure ()
solveVal _ it v | Left msg <- doesntOccur it v =
    -- TODO: Not all occurrences are toxic. The end could be in an argument
    -- to a hoping variable which isn't used.
    -- E.g. h1 = h2 h1 - this is valid if h2 is the identity, or ignores h1.
    err msg
solveVal Nat it@(InEnd inn) v@(VNum nv) = do
  dangling <- buildNatVal nv
  req (Wire (end dangling, TNat, inn))
  defineEnd "solveValNat" it v
solveVal _ it v = defineEnd "solveVal" it v
  -- Do we also need dummy wiring here?

solveSem :: TypeKind -> End -> Sem -> Checking ()
solveSem k hope = quote Zy >=> solveVal k hope

-- Convert a pattern into a value for the purposes of solving it with unification
-- for pattern matching. This is used for checking type constructors - we're only
-- dealing in static information.
valPat2Val :: TypeKind
           -> ValPat
           -> Checking (Bwd (Val Z) -- Values of the pattern vars
                       ,Val Z  -- The value of the whole pattern
                       )
valPat2Val k VPVar = do
  (_, [(idTgt, _)], [_], _) <- anext "pat2val" Id (S0, Some (Zy :* S0)) (REx ("", k) R0) (REx ("", k) R0)
  let val = VApp (VPar (toEnd idTgt)) B0
  pure (B0 :< val, val)
valPat2Val (TypeFor m _) (VPCon con args) = do
  ks <- fmap snd <$> tlup (m, con)
  (stk, args) <- valPats2Val ks args
  let val = VCon con args
  pure (stk, val)
valPat2Val Nat (VPNum n) = numPat2Val n >>= \(stk, nv) -> pure (stk, VNum nv)
 where
  numPat2Val :: NumPat -> Checking (Bwd (Val Z), NumVal (VVar Z))
  numPat2Val NP0 = pure (B0, nZero)
  numPat2Val (NP1Plus np) = second (nPlus 1) <$> numPat2Val np
  numPat2Val (NP2Times np) = second (n2PowTimes 1) <$> numPat2Val np
  numPat2Val NPVar = do
    (_, [(idTgt, _)], [_], _) <- anext "numpat2val" Id (S0, Some (Zy :* S0)) (REx ("", Nat) R0) (REx ("", Nat) R0)
    let var = endVal Nat (toEnd idTgt)
    pure (B0 :< var, nVar (VPar (toEnd idTgt)))

valPats2Val :: [TypeKind]
            -> [ValPat]
            -> Checking (Bwd (Val Z) -- Values of the pattern vars
                        ,[Val Z]  -- The value of the whole pattern
                        )
valPats2Val (k:ks) (v:vs) = do
  (stk, v) <- valPat2Val k v
  (stk', vs) <- valPats2Val ks vs
  pure (stk <+ stk', v:vs)
valPats2Val [] [] = pure (B0, [])
valPats2Val _ _ = err $ InternalError "Type args didn't match expected - kindCheck should've sorted it"

traceChecking :: (Show a, Show b) => String -> (a -> Checking b) -> (a -> Checking b)
traceChecking lbl m a = do
  traceM ("Enter " ++ lbl ++ ": " ++ show a)
  b <- m a
  traceM ("Exit  " ++ lbl ++ ": " ++ show b)
  pure b

--traceChecking = const id

dollarAndItsPrefix :: Bwd (String, Int) -> Maybe (Bwd (String, Int), String)
dollarAndItsPrefix B0 = Nothing
dollarAndItsPrefix (siz :< ('$':doll, _)) = Just (siz, doll)
dollarAndItsPrefix (siz :< _) = dollarAndItsPrefix siz

prefixLeftOf :: Bwd (String, Int) -> String -> Maybe (Bwd (String, Int))
prefixLeftOf B0 _ = Nothing
prefixLeftOf (siz :< (s, _)) key
  | s == key = Just siz
  | otherwise = prefixLeftOf siz key

allowedToSolve :: Bwd (String, Int) -> End -> Maybe String
allowedToSolve me it =
  let MkName itFwd = endName it
      itBwd = (B0 <>< itFwd)
  in  case (it, dollarAndItsPrefix me, dollarAndItsPrefix itBwd) of
        -- Solving a hope
        (InEnd _, Just (region, "rhs"), Just (maker, "!"))
          | Just region == prefixLeftOf maker "$rhs"
           ->
          trackPermission ("Allowed to solve:\n  " ++ show me ++ " / " ++ show it)
          $ Just "$!"
        -- We can only solve dangling wires when doing pattern matching in `solve`
        (_, Just (region, "lhs"), Just (region', "lhs"))
          | region == region'
          -> trackPermission ("Allowed to solve:\n  " ++ show me ++ " / " ++ show it)
          $ Just "gen"
        _ -> trackPermission ("Forbidden to solve:\n  " ++ show me ++ " / " ++ show it)
          Nothing

mineToSolve :: Checking (End -> Maybe String)
mineToSolve = allowedToSolve <$> whoAmI

-- Don't call this on kinds
-- Note: We can't really tell whether there's any prospect of the variable becoming
-- defined - if we could we could give a better error when something that wont be
-- defined is passed in.
awaitTypeDefinition :: Val Z -> Checking (Val Z)
awaitTypeDefinition ty = eval S0 ty >>= \case
  VApp (VPar e) _ -> mkYield "awaitTypeDefinition" (S.singleton e) >> awaitTypeDefinition ty
  ty -> pure ty
