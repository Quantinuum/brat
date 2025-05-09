{-# LANGUAGE AllowAmbiguousTypes #-}

module Brat.Checker.Helpers {-(pullPortsRow, pullPortsSig
                            ,simpleCheck
                            ,combineDisjointEnvs
                            ,ensureEmpty, noUnders
                            ,rowToSig
                            ,showMode, getVec
                            ,wire
                            ,next, knext, anext
                            ,kindType, getThunks
                            ,binderToValue, valueToBinder
                            ,kConFields
                            ,defineSrc, defineTgt
                            ,declareSrc, declareTgt
                            ,makeBox
                            ,uncons
                            ,evalBinder
                            ,evalSrcRow, evalTgtRow
                            )-} where

import Brat.Checker.Monad (Checking, CheckingSig(..), captureOuterLocals, err, typeErr, kindArgRows, defineEnd)
import Brat.Checker.Types
import Brat.Error (ErrorMsg(..))
import Brat.Eval (eval, EvMode(..), kindType)
import Brat.FC (FC)
import Brat.Graph (Node(..), NodeType(..))
import Brat.Naming (Name, FreshMonad(..))
import Brat.Syntax.CircuitProperties (CircuitProperties(..), Properties)
import Brat.Syntax.Common hiding (pattern PNone)
import Brat.Syntax.Core (Term(..))
import Brat.Syntax.Simple
import Brat.Syntax.Port (ToEnd(..))
import Brat.Syntax.Value
import Bwd
import Hasochism
import Util (log2)

import Control.Monad (when)
import Control.Monad.State.Lazy (StateT(..), runStateT)
import Control.Monad.Freer (req)
import Data.Bifunctor
import Data.Foldable (foldrM)
import Data.List (partition)
import Data.Type.Equality (TestEquality(..), (:~:)(..))
import qualified Data.Map as M
import Prelude hiding (last)

simpleCheck :: Modey m -> Val Z -> SimpleTerm -> Either ErrorMsg ()
simpleCheck Braty TNat (Num n) | n >= 0 = pure ()
simpleCheck Braty TInt (Num _) = pure ()
simpleCheck Braty TFloat (Float _) = pure ()
simpleCheck Braty TText (Text _) = pure ()
simpleCheck _ ty tm = Left $ TypeErr $ unwords
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

pullPorts :: forall a ty
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

noUnders m = do
  ((outs, ()), (overs, unders)) <- m
  ensureEmpty "unders" unders
  pure (outs, overs)

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

anext :: forall m i j k
       . EvMode m
      => String
      -> NodeType m
      -> (Semz i, Some Endz)
      -> Ro m i j -- Inputs and Outputs use de Bruijn indices
      -> Ro m j k
      -> Checking (Name, Unders m Chk, Overs m UVerb, (Semz k, Some Endz))
anext str th vals0 ins outs = do
  node <- req (Fresh str) -- Pick a name for the thunk
  -- Use the new name to generate Ends with which to instantiate types
  (unders, vals1) <- endPorts node InEnd In 0 vals0 ins
  (overs, vals2)  <- endPorts node ExEnd Ex 0 vals1 outs
  () <- sequence_ $
        [ declareTgt tgt (modey @m) ty | (tgt, ty) <- unders ] ++
        [ declareSrc src (modey @m) ty | (src, ty) <- overs ]
  let inputs  = [ (portName p, biType @m ty) | (p, ty) <- unders ]
  let outputs = [ (portName p, biType @m ty) | (p, ty) <- overs  ]

  () <- req (AddNode node (mkNode (modey @m) th inputs outputs))
  pure (node, unders, overs, vals2)
 where
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
          -> Properties m
          -> [(Src, BinderType Brat)] -- A row of 0 or more function types in the same mode
          -> Checking ([Name]
                      ,Unders m Chk
                      ,Overs m UVerb
                      )
getThunks _ _ [] = pure ([], [], [])
getThunks Braty () ((src, Right ty):rest) = do
  ty <- eval S0 ty
  (src, ss :->> ts) <- vectorise Braty (src, ty)
  (node, unders, overs, _) <- let ?my = Braty in
                                anext "Eval" (Eval (end src)) (S0, Some (Zy :* S0)) ss ts
  (nodes, unders', overs') <- getThunks Braty () rest
  pure (node:nodes, unders <> unders', overs <> overs')
getThunks Kerny expectedProps ((src, Right ty):rest) = do
  ty <- eval S0 ty
  (src, sig@(FunTy props ss ts)) <- vectorise Kerny (src,ty)
  when (props < expectedProps)
    (err (TypeErr (unwords ["Expected all kernel types to be"
                           ,expected expectedProps
                           ,"but kernel with signature"
                           ,show sig
                           ,"was"
                           ,actual props
                           ])))
  (node, unders, overs, _) <- let ?my = Kerny in anext "Splice" (Splice (end src)) (S0, Some (Zy :* S0)) ss ts
  (nodes, unders', overs') <- getThunks Kerny props rest
  pure (node:nodes, unders <> unders', overs <> overs')
 where
  expected PControllable = "controllable and reversible"
  expected PReversible = "reversible"
  expected _ = undefined

  actual PNone = "neither"
  actual PReversible = "just reversible, not controllable"
  actual _ = undefined

getThunks Braty () ((src, Left (Star args)):rest) = do
  (node, unders, overs) <- case bwdStack (B0 <>< args) of
    Some (_ :* stk) -> do
      let (ri,ro) = kindArgRows stk
      (node, unders, overs, _) <- next "Eval" (Eval (end src)) (S0, Some (Zy :* S0)) ri ro
      pure (node, unders, overs)
  (nodes, unders', overs') <- getThunks Braty () rest
  pure (node:nodes, unders <> unders', overs <> overs')
getThunks m _ ro = err $ ExpectedThunk (showMode m) (showRow ro)

-- The type given here should be normalised
vecLayers :: Modey m -> Val Z -> Checking ([(Src, NumVal (VVar Z))] -- The sizes of the vector layers
                                          ,FunTy m Z -- The function type at the end
                                          )
vecLayers my (TVec ty (VNum n)) = do
  src <- mkStaticNum n
  first ((src, n):) <$> vecLayers my ty
vecLayers Braty (VFun Braty cty) = pure ([], cty)
vecLayers Kerny (VFun Kerny cty) = pure ([], cty)
vecLayers my ty = typeErr $ "Expected a " ++ showMode my ++ "function or vector of functions, got " ++ show ty

mkStaticNum :: NumVal (VVar Z) -> Checking Src
mkStaticNum n@(NumValue c gro) = do
  (_, [], [(constSrc,_)], _) <- next "const" (Const (Num (fromIntegral c))) (S0, Some (Zy :* S0)) R0 (RPr ("value", TNat) R0)
  src <- case gro of
    Constant0 -> pure constSrc
    StrictMonoFun sm -> do
      (_, [(lhs,_),(rhs,_)], [(src,_)], _) <- next "add_const" (ArithNode Add) (S0, Some (Zy :* S0))
                                              (RPr ("lhs", TNat) (RPr ("rhs", TNat) R0))
                                              (RPr ("value", TNat) R0)
      smSrc <- mkStrictMono sm
      wire (constSrc, TNat, lhs)
      wire (smSrc, TNat, rhs)
      pure src
  defineSrc src (VNum n)
  pure src
 where
  mkStrictMono :: StrictMono (VVar Z) -> Checking Src
  mkStrictMono (StrictMono k mono) = do
    (_, [], [(constSrc,_)], _) <- next "2^k" (Const (Num (2^k))) (S0, Some (Zy :* S0)) R0 (RPr ("value", TNat) R0)
    (_, [(lhs,_),(rhs,_)], [(src,_)], _) <- next "mult_const" (ArithNode Mul) (S0, Some (Zy :* S0))
                                            (RPr ("lhs", TNat) (RPr ("rhs", TNat) R0))
                                            (RPr ("value", TNat) R0)
    monoSrc <- mkMono mono
    wire (constSrc, TNat, lhs)
    wire (monoSrc, TNat, rhs)
    pure src

  mkMono :: Monotone (VVar Z) -> Checking Src
  mkMono (Linear (VPar (ExEnd e))) = pure (NamedPort e "mono")
  mkMono (Full sm) = do
    (_, [], [(twoSrc,_)], _) <- next "2" (Const (Num 2)) (S0, Some (Zy :* S0)) R0 (RPr ("value", TNat) R0)
    (_, [(lhs,_),(rhs,_)], [(powSrc,_)], _) <- next "2^" (ArithNode Pow) (S0, Some (Zy :* S0))
                                               (RPr ("lhs", TNat) (RPr ("rhs", TNat) R0))
                                               (RPr ("value", TNat) R0)
    smSrc <- mkStrictMono sm
    wire (twoSrc, TNat, lhs)
    wire (smSrc, TNat, rhs)

    (_, [], [(oneSrc,_)], _) <- next "1" (Const (Num 1)) (S0, Some (Zy :* S0)) R0 (RPr ("value", TNat) R0)
    (_, [(lhs,_),(rhs,_)], [(src,_)], _) <- next "n-1" (ArithNode Sub) (S0, Some (Zy :* S0))
                                            (RPr ("lhs", TNat) (RPr ("rhs", TNat) R0))
                                            (RPr ("value", TNat) R0)
    wire (powSrc, TNat, lhs)
    wire (oneSrc, TNat, rhs)
    pure src

vectorise :: forall m. Modey m -> (Src, Val Z) -> Checking (Src, FunTy m Z)
vectorise my (src, ty) = do
  (layers, cty) <- vecLayers my ty
  modily my $ foldrM mkMapFun (src, cty) layers
 where
  mkMapFun :: (Src, NumVal (VVar Z)) -- Layer to apply
            -> (Src, FunTy m Z) -- The input to this level of mapfun
            -> Checking (Src, FunTy m Z)
  mkMapFun (lenSrc, len) (valSrc, cty) = do
    let weak1 = changeVar (Thinning (ThDrop ThNull))
    vecFun <- vectorisedFun len my cty
    (_, [(lenTgt,_), (valTgt, _)], [(vectorSrc, Right (VFun my' cty))], _) <-
      next "MapFun" MapFun (S0, Some (Zy :* S0))
      (REx ("len", Nat) (RPr ("value", weak1 ty) R0))
      (RPr ("vector", weak1 vecFun) R0)
    defineTgt lenTgt (VNum len)
    wire (lenSrc, kindType Nat, lenTgt)
    wire (valSrc, ty, valTgt)
    let vecFunTy = case (my,my',cty) of
          (Braty,Braty,cty) -> cty
          (Kerny,Kerny,cty) -> cty
          _ -> error "next returned wrong mode of computation type to that passed in"
    pure (vectorSrc, vecFunTy)

  vectorisedFun :: NumVal (VVar Z) -> Modey m -> FunTy m Z -> Checking (Val Z)
  vectorisedFun nv my (FunTy ps ss ts) = do
    (ss', ny) <- vectoriseRo True nv Zy ss
    (ts', _)  <- vectoriseRo False nv ny ts
    pure $ modily my $ VFun my (FunTy ps ss' ts')

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
defineSrc src = defineEnd (ExEnd (end src))

defineTgt :: Tgt -> Val Z -> Checking ()
defineTgt tgt = defineEnd (InEnd (end tgt))

declareSrc :: Src -> Modey m -> BinderType m -> Checking ()
declareSrc src my ty = req (Declare (ExEnd (end src)) my ty)

declareTgt :: Tgt -> Modey m -> BinderType m -> Checking ()
declareTgt tgt my ty = req (Declare (InEnd (end tgt)) my ty)

-- listToRow :: [(PortName, BinderType m)] -> Ro m Z i
-- listToRow [] = R0
-- listToRow ((

-- Build a box corresponding to the inside of a thunk
makeBox :: (?my :: Modey m, EvMode m)
        => String -- A label for the nodes we create
        -> FunTy m Z
        -> ((Overs m UVerb, Unders m Chk) -> Checking a) -- checks + builds the body using srcs/tgts from the box
        -> Checking ((Src, BinderType Brat), a)
makeBox name cty@(FunTy _ ss ts) body = do
  (src, _, overs, ctx) <- anext (name ++ "/in") Source (S0, Some (Zy :* S0)) R0 ss
  (tgt, unders, _, _) <- anext (name ++ "/out") Target ctx ts R0
  case (?my, body) of
    (Kerny, _) -> do
      (_,_,[thunk],_) <- next (name ++ "_thunk") (Box M.empty src tgt) (S0, Some (Zy :* S0))
                                R0 (RPr ("thunk", VFun Kerny cty) R0)
      bres <- name -! body (overs, unders)
      pure (thunk, bres)
    (Braty, body) -> do
      (bres, captures) <- name -! captureOuterLocals (body (overs, unders))
      (_, [], [thunk], _) <- next (name ++ "_thunk") (Box captures src tgt) (S0, Some (Zy :* S0))
                                     R0 (RPr ("thunk", VFun ?my cty) R0)
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

buildConst :: SimpleTerm -> Val Z -> Checking Src
buildConst tm ty = do
  (_, _, [(out,_)], _) <- next "buildConst" (Const tm) (S0, Some (Zy :* S0)) R0 (RPr ("value", ty) R0)
  pure out
