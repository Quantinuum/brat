-- TODO: Remove DFG children of case nodes. Case nodes have inputs and outputs, so they *are* the DFG
-- possibly we need to be smart about compiling DFGs for this
-- they're getting the boxes as arguments

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Brat.Compile.Hugr (compile) where

import Brat.Constructors.Patterns (pattern CFalse, pattern CTrue)
import Brat.Checker.Monad (track, trackM, CheckingSig(..), CaptureSets)
import Brat.Checker.Helpers (binderToValue)
import Brat.Checker.Types (Store(..), VEnv)
import Brat.Eval (eval, evalCTy, kindType)
import Brat.Graph hiding (lookupNode)
import Brat.Naming
import Brat.QualName
import Brat.Syntax.Port
import Brat.Syntax.Common
import Brat.Syntax.Simple (SimpleTerm)
import Brat.Syntax.Value
import Bwd
import Control.Monad.Freer
import Data.Hugr
import Data.HugrGraph (HugrGraph, Container(..), NodeId)
import qualified Data.HugrGraph as H
import Hasochism

import Control.Monad (unless)
import Data.Aeson
import Data.Bifunctor (first, second)
import qualified Data.ByteString.Lazy as BS
import Data.Foldable (traverse_, for_)
import Data.Functor ((<&>), ($>))
import Data.List (sortBy)
import qualified Data.Map as M
import Data.Maybe (catMaybes, fromJust)
import Data.Ord (comparing)
import Data.Traversable (for)
import Control.Monad.State
import Data.List.NonEmpty (NonEmpty, nonEmpty)
import GHC.Base (NonEmpty(..))

{-
For each top level function definition or value in BRAT: we should have a FuncDef node in
hugr, whose child graph is the body of the function
-}

type TypedPort = (PortId NodeId, HugrType)

data CompilationState = CompilationState
 { bratGraph :: Graph -- the input BRAT Graph; should not be written
 , capSets :: CaptureSets -- environments captured by Box nodes in previous
 , hugr :: HugrGraph
 , compiled :: M.Map Name NodeId  -- Mapping from Brat nodes to Hugr nodes
 -- When lambda lifting, captured variables become extra function inputs.
 -- This maps from the captured value (in the BRAT graph, perhaps outside the current func/lambda)
 -- to the Hugr port capturing it in the current context.
 , liftedOutPorts :: M.Map OutPort (PortId NodeId)
 , holes :: Bwd Name -- for Kernel graphs, list of Splices found in order
 , store :: Store -- Kinds and values of global variables, for compiling types
 -- A map from Id nodes representing functions and values in the brat graph,
 -- to the FuncDef nodes that we create for them. The bool, if true, says that
 -- we must insert an *extra* call, beyond what's required in Brat, to compute the value
 -- of the decl (e.g. `x :: Int` `x = 1+2` requires calling the FuncDefn to calculate 1+2).
 -- Note that in the future this could be extended to allow top-level Consts too.
 , decls :: M.Map Name (NodeId, Bool)
 }

makeCS :: (Graph, CaptureSets, Store) -> HugrGraph -> CompilationState
makeCS (g, cs, store) hugr =
  CompilationState
    { bratGraph = g
    , capSets = cs
    , hugr = hugr
    , compiled = M.empty
    , holes = B0
    , liftedOutPorts = M.empty
    , store = store
    , decls = M.empty
    }

registerFuncDef :: Name -> (NodeId, Bool) -> Compile ()
registerFuncDef name hugrDef = do
  st <- get
  put (st { decls = M.insert name hugrDef (decls st) })

freshNode :: String -> NodeId -> Compile NodeId
freshNode name parent = do
  s <- get
  let (id, h) = H.freshNode (hugr s) parent name
  put s {hugr = h}
  pure id

freshNodeWithIO :: String -> NodeId -> Compile Container
freshNodeWithIO name parent = do
  ctr <- freshNode name parent
  input <- freshNode (name ++ "_Input") ctr
  output <- freshNode (name ++ "_Input") ctr
  s <- get
  put s {hugr = H.setFirstChildren (hugr s) ctr [input, output]}
  pure $ Ctr ctr input output

addEdge :: (PortId NodeId, PortId NodeId) -> Compile ()
addEdge e = get >>= \st -> put (st { hugr = H.addEdge (hugr st) e })

addNode :: String -> (NodeId, HugrOp) -> Compile NodeId
addNode nam (parent, op) = do
  name <- freshNode nam parent
  setOp name (addMetadata [("id", show name)] op)
  pure name

type Compile = State CompilationState

runCheckingInCompile :: Free CheckingSig t -> Compile t
runCheckingInCompile (Ret t) = pure t
runCheckingInCompile (Req (ELup e) k) = do
  emap <- gets (valueMap . store)
  runCheckingInCompile (k (M.lookup e emap))
runCheckingInCompile (Req _ _) = error "Compile monad found a command it can't handle"

-- To be called on top-level signatures which are already Inx-closed, but not
-- necessarily normalised.
compileSig :: Modey m -> CTy m Z -> Compile ([HugrType], [HugrType])
compileSig my cty = runCheckingInCompile (evalCTy S0 my cty) <&> (\(ss :->> ts) -> (compileRo ss, compileRo ts))

compileCTy (ss :->> ts) = PolyFuncType [] (FunctionType (compileRo ss) (compileRo ts) bratExts)

compileRo :: Ro m i j -- The Ro that we're processing
          -> [HugrType]       -- The hugr type of the row
compileRo R0 = []
compileRo (RPr (_, ty) ro) = compileType ty:compileRo ro
compileRo (REx (_, k) ro) = compileType (kindType k):compileRo ro

-- Val Z should already be eval'd at this point
compileType :: Val n -> HugrType
compileType TQ = HTQubit
compileType TMoney = HTQubit
compileType TBit = HTSum (SU (UnitSum 2))
compileType TBool = HTSum (SU (UnitSum 2))
compileType TInt = hugrInt
compileType TNat = hugrInt
compileType TFloat = hugrFloat
compileType ty@(TCons _ _) = htTuple (tuple ty)
 where
  tuple :: Val n -> [HugrType]
  tuple (TCons hd rest) = compileType hd:tuple rest
  tuple TNil = []
  tuple ty = error $ "Found " ++ show ty  ++ " in supposed tuple type"
compileType TNil = htTuple []
compileType (TVec el _) = hugrList (compileType el)
compileType (TList el)  = hugrList (compileType el)
-- All variables are of kind `TypeFor m xs`, we already checked in `kindCheckRow`
compileType (VApp _ _) = htTuple []
-- VFun is already evaluated here, so we don't need to call `compileSig`
compileType (VFun _ cty) = HTFunc $ compileCTy cty
compileType ty = error $ "todo: compile type " ++ show ty

compileGraphTypes :: Traversable t => t (Val Z) -> Compile (t HugrType)
compileGraphTypes = traverse ((<&> compileType) . runCheckingInCompile . eval S0)

-- Compile a list of types from the inputs or outputs of a node in the BRAT graph
compilePorts :: [(a, Val Z)] -> Compile [HugrType]
compilePorts = compileGraphTypes . map snd

setOp :: NodeId -> HugrOp -> Compile ()
setOp name op | track ("addOp " ++ show op ++ show name) False = undefined
setOp name op = get >>= \st -> put (st { hugr = H.setOp (hugr st) name op })

registerCompiled :: Name -> NodeId -> Compile ()
registerCompiled from to | track (show from ++ " |-> " ++ show to) False = undefined
registerCompiled from to = do
  st <- get
  let new_compiled = M.alter (\Nothing -> Just to) from (compiled st)
  put (st { compiled = new_compiled })

compileConst :: NodeId -> SimpleTerm -> HugrType -> Compile NodeId
compileConst parent tm ty = do
  constId <- addNode "Const" (parent, OpConst (ConstOp (valFromSimple tm)))
  loadId <- case ty of
    HTFunc poly@(PolyFuncType [] _) ->
      addNode "LoadFunction" (parent, OpLoadFunction (LoadFunctionOp poly [] (FunctionType [] [HTFunc poly] [])))
    HTFunc (PolyFuncType _ _) -> error "Trying to compile function with type args"
    _ -> addNode "LoadConst" (parent, OpLoadConstant (LoadConstantOp ty))
  addEdge (Port constId 0, Port loadId 0)
  pure loadId

compileArithNode :: NodeId -> ArithOp -> Val Z -> Compile NodeId
compileArithNode parent op TNat  = addNode (show op ++ "_Nat") (parent, OpCustom $ case op of
  Add -> binaryIntOp "iadd"
  Sub -> binaryIntOp "isub"
  Mul-> binaryIntOp "imul"
  Div -> intOp "idiv_u" [hugrInt, hugrInt] [hugrInt] [TANat intWidth, TANat intWidth]
  Pow -> error "TODO: Pow"  -- Not defined in extension
 )
compileArithNode parent op TInt = addNode (show op ++ "_Int") (parent, OpCustom $ case op of
  Add -> binaryIntOp "iadd"
  Sub -> binaryIntOp "isub"
  Mul-> binaryIntOp "imul"
  Div -> intOp "idiv_u" [hugrInt, hugrInt] [hugrInt] [TANat intWidth, TANat intWidth]
  Pow -> error "TODO: Pow"  -- Not defined in extension
 )
compileArithNode parent op TFloat = addNode (show op ++ "_Float") (parent, OpCustom $ case op of
  Add -> binaryFloatOp "fadd"
  Sub -> binaryFloatOp "fsub"
  Mul-> binaryFloatOp "fmul"
  Div-> binaryFloatOp "fdiv"
  Pow -> error "TODO: Pow"  -- Not defined in extension
 )
compileArithNode _ _ ty = error $ "compileArithNode: Unexpected type " ++ show ty

renameAndSortHugr :: HugrGraph -> Hugr Int
renameAndSortHugr hugr = H.serialize (foldl H.addOrderEdge hugr orderEdges)
 where
  orderEdges :: [(NodeId, NodeId)]
  orderEdges =
    -- Nonlocal edges (from a node to another which is a *descendant* of a sibling of the source)
    -- require an extra order edge from the source to the sibling that is ancestor of the target
    let interEdges = [(n1, n2) | (Port n1 _, Port n2 _) <- H.edgeList hugr,
            (parentOf n1 /= parentOf n2),
            requiresOrderEdge (H.getOp hugr n1),
            requiresOrderEdge (H.getOp hugr n2)] in
    track ("interEdges: " ++ show interEdges) (walkUp <$> interEdges)

  requiresOrderEdge :: HugrOp -> Bool
  requiresOrderEdge (OpMod _) = False
  requiresOrderEdge (OpDefn _) = False
  requiresOrderEdge (OpConst _) = False
  requiresOrderEdge _ = True

  parentOf = H.getParent hugr

  -- Walk up the hierarchy from the tgt until we hit a node at the same level as src
  walkUp :: (NodeId, NodeId) -> (NodeId, NodeId)
  walkUp (src, tgt) | parentOf src == parentOf tgt = (src, tgt)
  walkUp (_, tgt) | parentOf tgt == tgt = error "Tgt was not descendant of Src-parent"
  walkUp (src, tgt) = walkUp (src, parentOf tgt)

dumpJSON :: Compile BS.ByteString
dumpJSON = gets hugr <&> (encode . renameAndSortHugr) 

compileClauses :: NodeId -> [TypedPort] -> NonEmpty (TestMatchData m, Name) -> Compile [TypedPort]
compileClauses parent ins ((matchData, rhs) :| clauses) = do
  (ns, _) <- gets bratGraph
  -- RHS has to be a box, so it must have a function type
  outTys <- case nodeOuts (ns M.! rhs) of
    [(_, VFun my cty)] -> compileSig my cty >>= (\(_, outs) -> pure outs)
    _ -> error "Expected 1 kernel function type from rhs"

  -- Compile the match: testResult is the port holding the dynamic match result
  -- with the type `sumTy`
  let TestMatchData my matchSeq = matchData
  matchSeq <- compileGraphTypes (fmap (binderToValue my) matchSeq)

  let portTbl = zip (fst <$> matchInputs matchSeq) ins
  testResult <- compileMatchSequence parent portTbl matchSeq

  -- Feed the test result into a conditional
  makeConditional ("clause of " ++ show rhs) parent testResult [] [("didntMatch", didntMatch outTys)
                                                                  ,("didMatch", didMatch outTys)
                                                                  ]
 where
  didntMatch :: [HugrType] -> NodeId -> [TypedPort] -> Compile [TypedPort]
  didntMatch outTys parent ins = case nonEmpty clauses of
    Just clauses -> compileClauses parent ins clauses
    -- If there are no more clauses left to test, then the Hugr panics
    Nothing -> let sig = FunctionType (snd <$> ins) outTys ["BRAT"] in
      addNodeWithInputs "Panic" (parent, OpCustom (CustomOp "BRAT" "panic" sig [])) ins outTys

  didMatch :: [HugrType] -> NodeId -> [TypedPort] -> Compile [TypedPort]
  didMatch outTys parent ins = gets bratGraph >>= \(ns,_) -> case ns M.! rhs of
    BratNode (Box src tgt) _ _ -> do
      ctr <- freshNodeWithIO "DidMatch" parent
      let dfgId = H.parent ctr
      setOp dfgId (OpDFG (DFG (FunctionType (snd <$> ins) outTys bratExts) []))
      compileBox ctr (src, tgt)
      for_ (zip (fst <$> ins) (Port dfgId <$> [0..])) addEdge
      pure $ zip (Port dfgId <$> [0..]) outTys
    _ -> error "RHS should be a box node"

compileBox :: Container  -> (Name, Name) -> Compile ()
-- note: we used to compile only KernelNode's here, this may not be right
compileBox (Ctr parent srcN tgtN) (src, tgt) = do
  -- Compile Source
  node <- gets ((M.! src) . fst . bratGraph)
  trackM ("compileSource (" ++ show parent ++ ") " ++ show src ++ " " ++ show node)
  let src_outs = case node of
               (BratNode Source [] outs) -> outs
               (KernelNode Source [] outs) -> outs
  srcTys <- compilePorts src_outs
  setOp srcN (OpIn (InputNode srcTys [("source", "Source"), ("parent", show parent)]))
  registerCompiled src srcN
  compileTarget parent tgtN tgt

compileTarget :: NodeId -> NodeId -> Name -> Compile ()
compileTarget parent tgtN tgt = do
  node <- gets ((M.! tgt) . fst . bratGraph)
  trackM ("compileTarget (" ++ show parent ++ ") " ++ show tgt ++ " " ++ show node)
  let tgt_ins = case node of
               (BratNode Target ins []) -> ins
               (KernelNode Target ins []) -> ins
  tgtTys <- compilePorts tgt_ins
  setOp tgtN (OpOut (OutputNode tgtTys [("source", "Target")]))
  edges <- compileInEdges parent tgt
  -- registerCompiled tgt tgtN -- really shouldn't be necessary, not reachable
  for_ edges (\(src, tgtPort) -> addEdge (src, Port tgtN tgtPort))
  pure ()

in_edges :: Name -> Compile [((OutPort, Val Z), Int)]
in_edges name = gets bratGraph <&> \(_, es) -> [((src, ty), portNum) | (src, ty, In edgTgt portNum) <- es, edgTgt == name]

compileInEdges :: NodeId -> Name -> Compile [(PortId NodeId, Int)]
compileInEdges parent name = do
  in_edges <- in_edges name
  catMaybes <$> for in_edges (\((src, _), tgtPort) -> getOutPort parent src <&> fmap (, tgtPort))

compileWithInputs :: NodeId -> Name -> Compile (Maybe NodeId)
compileWithInputs parent name = gets (M.lookup name . compiled) >>= \case
  Just nid -> pure (Just nid)
  Nothing -> do
    compileNode >>= \case
      Nothing -> pure Nothing
      Just (tgtNodeId, edges) -> do
        registerCompiled name tgtNodeId
        for_ edges (\(src, tgtPort) -> addEdge (src, Port tgtNodeId tgtPort))
        pure $ Just tgtNodeId
 where
  -- If we only care about the node for typechecking, then drop it and return `Nothing`.
  -- Otherwise, NodeId of compiled node, and list of Hugr in-edges (source and target-port)
  compileNode :: Compile (Maybe (NodeId, [(PortId NodeId, Int)]))
  compileNode = case (hasPrefix ["checking", "globals", "decl"] name) of
    Just _ -> do
      -- reference to a top-level decl. Every such should be in the decls map.
      -- We need to return value of each type (perhaps to be indirectCalled by successor).
      -- Note this is where we must compile something different *for each caller* by clearing out the `compiled` map for each function
      hTys <- in_edges name <&> (map (compileType . snd . fst) . sortBy (comparing snd))

      decls <- gets decls
      let (funcDef, extra_call) = decls M.! name
      nod <- if extra_call
            then addNode ("direct_call(" ++ show funcDef ++ ")")
                          (parent, OpCall (CallOp (FunctionType [] hTys bratExts)))
            -- We are loading idNode as a value (not an Eval'd thing), and it is a FuncDef directly
            -- corresponding to a Brat TLD (not that produces said TLD when eval'd)
            else case hTys of
              [HTFunc poly@(PolyFuncType [] _)] ->
                addNode ("load_thunk(" ++ show funcDef ++ ")")
                (parent, OpLoadFunction (LoadFunctionOp poly [] (FunctionType [] [HTFunc poly] [])))
              [HTFunc (PolyFuncType args _)] -> error $ unwords ["Unexpected type args to"
                                                                ,show funcDef ++ ":"
                                                                ,show args
                                                                ]
              _ -> error $ "Expected a function argument when loading thunk, got: " ++ show hTys
      -- the only input
      pure $ Just (nod, [(Port funcDef 0, 0)])
    _ -> do
      (ns, _) <- gets bratGraph
      let node = ns M.! name
      trackM ("compileNode (" ++ show parent ++ ") " ++ show name ++ " " ++ show node)
      nod_edge_info <- case node of
        (BratNode thing ins outs) -> compileNode' thing ins outs
        (KernelNode thing ins outs) -> compileNode' thing ins outs
      case nod_edge_info of
        Nothing -> pure Nothing
        Just (node, tgtOffset, extra_edges) -> do
          trans_edges <- compileInEdges parent name <&> map (second (+tgtOffset))
          pure $ Just (node, extra_edges ++ trans_edges)

  default_edges :: NodeId -> Maybe (NodeId, Int, [(PortId NodeId, Int)])
  default_edges nid = Just (nid, 0, [])

  compileNode' :: NodeType m -> [(PortName, Val Z)] -> [(PortName, Val Z)]
                  -- Result is nodeid, port offset, *extra* edges
               -> Compile (Maybe (NodeId, Int, [(PortId NodeId, Int)]))
  compileNode' thing ins outs = case thing of
    Const tm -> default_edges <$> (compilePorts outs >>= (compileConst parent tm . head))
    Splice (Ex outNode _) -> default_edges <$> do
      ins <- compilePorts ins
      outs <- compilePorts outs
      let sig = FunctionType ins outs bratExts
      case hasPrefix ["checking", "globals", "prim"] outNode of
        -- If we're evaling a Prim, we add it directly into the kernel graph
        Just suffix -> do
          (ns, _) <- gets bratGraph
          case M.lookup outNode ns of
            Just (BratNode (Prim (ext,op)) _ [(_, VFun Kerny _)]) -> do
              addNode (show suffix) (parent, OpCustom (CustomOp ext op sig []))
            x -> error $ "Expected a Prim kernel node but got " ++ show x
        -- All other evaled things are turned into holes to be substituted later
        Nothing -> do
          hole <- do
            st <- get
            let h = holes st
            put (st { holes = h :< name})
            pure (length h)
          addNode ("hole " ++ show hole) (parent, OpCustom (holeOp hole sig))
    -- A reference to a primitive op which exists in hugr.
    -- This should only have one outgoing wire which leads to an `Id` node for
    -- the brat representation of the function, and that wire should have a
    -- function type
    Prim (ext,op) -> do
      let n = ext ++ ('_':op)
      let [] = ins
      -- TODO: Handle primitives which aren't functions
      let [(_, VFun Braty cty)] = outs
      boxSig@(inputTys, outputTys) <- compileSig Braty cty
      let boxFunTy = FunctionType inputTys outputTys bratExts
      ((Port loadConst _, _ty), ()) <- compileConstDfg parent n boxSig $ \ctr -> do
        setOp (H.input ctr) (OpIn (InputNode inputTys [("source", "Prim")]))
        let ins = zip (Port (H.input ctr) <$> [0..]) inputTys
        outs <- addNodeWithInputs n (H.parent ctr, OpCustom (CustomOp ext op boxFunTy [])) ins outputTys
        setOp (H.output ctr) (OpOut (OutputNode outputTys [("source", "Prim")]))
        for_ (zip (fst <$> outs) (Port (H.output ctr) <$> [0..])) addEdge
        pure ()
      pure $ default_edges loadConst

    -- Check if the node has prefix "globals", hence should be a direct call
    Eval tgt@(Ex outNode _) -> do
      ins <- compilePorts ins
      outs <- compilePorts outs
      (ns, _) <- gets bratGraph
      decls <- gets decls
      case hasPrefix ["checking", "globals", "prim"] outNode of
        -- Callee is a Prim node, insert Hugr Op; first look up outNode in the BRAT graph to get the Prim data
        Just suffix -> default_edges <$> case M.lookup outNode ns of
          Just (BratNode (Prim (ext,op)) _ _) -> do
            addNode (show suffix) (parent, OpCustom (CustomOp ext op (FunctionType ins outs [ext]) []))
          x -> error $ "Expected a Prim node but got " ++ show x
        Nothing -> case hasPrefix ["checking", "globals"] outNode of
          -- Callee is a user-defined global def that, since it does not require an "extra" call, can be turned from IndirectCall to direct.
          Just _ | (funcDef, False) <- fromJust (M.lookup outNode decls) -> do
                callerId <- addNode ("direct_call(" ++ show funcDef ++ ")")
                                    (parent, OpCall (CallOp (FunctionType ins outs bratExts)))
                -- Add the static edge from the FuncDefn node to the port *after*
                -- all of the dynamic arguments to the Call node.
                -- This is because in hugr, static edges (like the graph arg to a
                -- Call) come after dynamic edges
                pure $ Just (callerId, 0, [(Port funcDef 0, length ins)])
          -- Either not global, or we must evaluate the global -- so an indirect call of a graph on a wire
          -- (If it's a global, compileWithInputs will generate extra no-args Call,
          -- since extra_call==True; we just turned the (Eval+)LoadFunction case into a direct Call above)
          _ -> getOutPort parent tgt >>= \case
            Just funcPort@(Port calleeId _) -> do
              callerId <- addNode ("indirect_call(" ++ show calleeId ++ ")")
                                  (parent, OpCallIndirect (CallIndirectOp (FunctionType ins outs bratExts {-[]-})))
              -- for an IndirectCall, the callee (thunk, function value) is the *first*
              -- Hugr input. So move all the others along, and add that extra edge.
              pure $ Just (callerId, 1, [(funcPort, 0)])
            Nothing -> error "Callee has been erased"

    -- We need to figure out if this thunk contains a brat- or a kernel-computation
    (Box src tgt) -> case outs of
      [(_, VFun Kerny cty)] -> default_edges . nodeId . fst <$>
           compileKernBox parent (show name) (src, tgt) cty
      [(_, VFun Braty cty)] -> do
        cs <- gets (M.findWithDefault M.empty name . capSets)
        (partialNode, captures) <- compileBratBox parent name (cs, src, tgt) cty
        pure $ Just (partialNode, 1, captures) -- 1 is arbitrary, Box has no real inputs
      outs -> error $ "Unexpected outs of box: " ++ show outs

    Source -> error "Source found outside of compileBox"
      
    Target -> error "Target found outside of compileBox"

    Id | Nothing <- hasPrefix ["checking", "globals", "decl"] name -> default_edges <$> do
      -- not a top-level decl, just compile it as an Id (TLDs handled in compileNode)
      let [(_,ty)] = ins -- fail if more than one input
      addNode "Id" (parent, OpNoop (NoopOp (compileType ty)))

    Constructor c -> default_edges <$> do
      ins <- compilePorts ins
      case outs of
        [(_, VCon tycon _)] -> do
          outs <- compilePorts outs
          compileConstructor parent tycon c (FunctionType ins outs ["BRAT"])
    PatternMatch cs -> default_edges <$> do
      ins <- compilePorts ins
      outs <- compilePorts outs
      (Ctr dfgId inputNode outputNode) <- freshNodeWithIO "PatternMatch" parent
      setOp dfgId (OpDFG (DFG (FunctionType ins outs bratExts) []))
      setOp inputNode (OpIn (InputNode ins [("source", "PatternMatch"), ("parent", show dfgId)]))
      ccOuts <- compileClauses dfgId (zip (Port inputNode <$> [0..]) ins) cs
      setOp outputNode (OpOut (OutputNode (snd <$> ccOuts)  [("source", "PatternMatch"), ("parent", show dfgId)]))
      for_ (zip (fst <$> ccOuts) (Port outputNode <$> [0..])) addEdge
      pure dfgId
    ArithNode op -> default_edges <$> compileArithNode parent op (snd $ head ins)
    Selector _c -> error "Todo: selector"
    Replicate -> default_edges <$> do
      ins <- compilePorts ins
      let [_, elemTy] = ins
      outs <- compilePorts outs
      let sig = FunctionType ins outs bratExts
      addNode "Replicate" (parent, OpCustom (CustomOp "BRAT" "Replicate" sig [TAType elemTy]))
    x -> error $ show x ++ " should have been compiled outside of compileNode"

compileConstructor :: NodeId -> QualName -> QualName -> FunctionType -> Compile NodeId
compileConstructor parent tycon con sig
  | Just b <- isBool con = do
      -- A boolean value is a tag which takes no inputs and produces an empty tuple
      -- This is the same thing that happens in Brat.Checker.Clauses to make the
      -- discriminator (makeRowTag)
      addNode "bool.tag" (parent, OpTag (TagOp (if b then 1 else 0) [[], []] [("hint", "bool")]))
  | otherwise = let name = "Constructor " ++ show tycon ++ "::" ++ show con in
                  addNode name (parent, constructorOp tycon con sig)
 where
  isBool :: QualName -> Maybe Bool
  isBool CFalse = Just False
  isBool CTrue = Just True
  isBool _ = Nothing


getOutPort :: NodeId -> OutPort -> Compile (Maybe (PortId NodeId))
getOutPort parent p@(Ex srcNode srcPort) = do
    -- Check if we should actually be using a different port because we're
    -- inside a lambda-lifted function and src comes in from the outside?
    lifted <- gets liftedOutPorts
    trackM $ show lifted
    case M.lookup p lifted of
      Just intercept -> pure $ Just intercept
      Nothing -> compileWithInputs parent srcNode <&> (\maybe -> maybe <&> flip Port srcPort)

-- Execute a compilation (which takes a DFG parent) in a nested monad;
-- produce a Const node containing the resulting Hugr, and a LoadConstant,
-- and return the latter.
compileConstDfg :: NodeId -> String -> ([HugrType], [HugrType]) -> (Container -> Compile a) -> Compile (TypedPort, a)
compileConstDfg parent desc (inTys, outTys) contents = do
  st <- gets store
  g <- gets bratGraph
  cs <- gets capSets
  let funTy = FunctionType inTys outTys bratExts
  -- First, we fork off a new namespace
  s <- get
  let (nsx, hugr') = H.splitNamespace (hugr s) desc
  put s {hugr=hugr'}
  -- And pass that namespace into nested monad that compiles the DFG
  let (h, ctr) = H.newWithIO nsx ("Box_" ++ show desc) (OpDFG $ DFG funTy [])
  let (a, compState) = runState (contents ctr) (makeCS (g,cs,st) h)
  let nestedHugr = renameAndSortHugr (hugr compState)
  let ht = HTFunc $ PolyFuncType [] funTy

  constNode <- addNode ("ConstTemplate_" ++ desc) (parent, OpConst (ConstOp (HVFunction nestedHugr)))
  lcPort <- head <$> addNodeWithInputs ("LoadTemplate_" ++ desc) (parent, OpLoadConstant (LoadConstantOp ht))
            [(Port constNode 0, ht)] [ht]
  pure (lcPort, a)

-- Brat computations may capture some local variables. Thus, we need
-- to lambda-lift, producing (as results) a Partial node and a list of
-- extra arguments i.e. the captured values
compileBratBox :: NodeId -> Name -> (VEnv, Name, Name) -> CTy Brat Z -> Compile (NodeId, [(PortId NodeId, Int)])
compileBratBox parent name (venv, src, tgt) cty = do
  -- we'll "Partial" over every value in the environment.
  -- (TODO in the future capture which ones are actually used in the sub-hugr. We may need
  -- to put captured values after the original params, and have a reversed Partial.)
  let params :: [(OutPort, BinderType Brat)] = map (first end) (concat $ M.elems venv)
  parmTys <- compileGraphTypes (map (binderToValue Braty . snd) params)

  -- Create a FuncDefn for the lambda that takes the params as first inputs
  (inputTys, outputTys) <- compileSig Braty cty
  let allInputTys = parmTys ++ inputTys
  let boxInnerSig = FunctionType allInputTys outputTys bratExts

  (templatePort, _) <- compileConstDfg parent ("BB" ++ show name) (allInputTys, outputTys) $ \ctr -> do
    let src_id = H.input ctr -- would be good to name "LiftedCapturedInputs"
    setOp src_id (OpIn (InputNode allInputTys [("source", "compileBratBox")]))
    -- Now map ports in the BRAT Graph to their Hugr equivalents.
          -- Each captured value is read from an element of src_id, starting from 0
    let lifted = [(src, Port src_id i) | ((src, _ty), i) <- zip params [0..]]
          -- and the original BRAT-Graph Src outports become the Hugr Input node ports *after* the captured values
          ++ [(Ex src i, Port src_id (i + length params)) | i <- [0..length inputTys]]
    st <- get
    put $ st {liftedOutPorts = M.fromList lifted}
    -- no need to return any holes
    compileTarget (H.parent ctr) (H.output ctr) tgt

  -- Finally, we add a `Partial` node to supply the captured params.
  partialNode <- addNode "Partial" (parent, OpCustom $ partialOp boxInnerSig (length params))
  addEdge (fst templatePort, Port partialNode 0)
  edge_srcs <- for (map fst params) $ getOutPort parent
  pure (partialNode, zip (map fromJust edge_srcs) [1..])
    -- error on Nothing, the Partial is expecting a value

compileKernBox :: NodeId -> String -> (Name, Name) -> CTy Kernel Z -> Compile TypedPort
compileKernBox parent desc src_tgt cty = do
  -- compile kernel nodes only into a Hugr with "Holes"
  -- when we see a Splice, we'll record the func-port onto a list
  -- return a Hugr with holes
  boxInnerSig@(inTys, outTys) <- compileSig Kerny cty
  let boxTy = HTFunc $ PolyFuncType [] (FunctionType inTys outTys bratExts)
  (templatePort, holelist) <- compileConstDfg parent ("KB" ++ desc) boxInnerSig $ \ctr -> do
    compileBox ctr src_tgt
    gets holes

  -- For each hole in the template (index 0 i.e. earliest, first)
  -- compile the kernel that should be spliced in and record its signature.
  ns <- gets (fst . bratGraph)
  hole_ports <- for (holelist <>> []) (\splice -> do
    let (KernelNode (Splice kernel_src) ins outs) = ns M.! splice
    ins <- compilePorts ins
    outs <- compilePorts outs
    kernel_src <- getOutPort parent kernel_src <&> fromJust
    pure (kernel_src, HTFunc (PolyFuncType [] (FunctionType ins outs bratExts))))

  -- Add a substitute node to fill the holes in the template
  let hole_sigs = [ body poly | (_, HTFunc poly) <- hole_ports ]
  head <$> addNodeWithInputs ("subst_" ++ desc) (parent, OpCustom (substOp (FunctionType inTys outTys bratExts) hole_sigs)) (templatePort : hole_ports) [boxTy]


-- We get a bunch of TypedPorts which are associated with Srcs in the BRAT graph.
-- Then, we'll perform a sequence of matches on those ports
-- Return a sum whose first component is the types we started with in the order
-- specified by the portTable argument.
--
-- In the happy path we return wires in the order of `matchOutputs`
-- otherwise, the order is the same as how they came in via the portTable
compileMatchSequence :: NodeId -- The parent node
                     -> [(Src  -- Things we've matched or passed through, coming from an Input node
                         ,TypedPort)] -- This portTable and `matchInputs` should be in the same order
                     -> MatchSequence HugrType
                     -> Compile TypedPort
compileMatchSequence parent portTable (MatchSequence {..}) = do
  unless
    ((second snd <$> portTable) == matchInputs)
    (error "compileMatchSequence assert failed")
  let sumTy = SoR [snd <$> matchInputs, snd <$> matchOutputs]
  case matchTests of
    (src, primTest):tests -> do
      -- Pick the port corresponding to the source we want to test
      let ((_, typedPort), (left, right)) = head $ filter ((src ==) . fst . fst) (foci portTable)
      let others = left <>> right
      -- Compile the primitive test, giving us a single `testResult` port with a
      -- sum type (either the thing we looked at or it's pieces) and a bunch of
      -- other inputs
      testResult <- compilePrimTest parent typedPort primTest
      let testIx = length left
      let remainingMatchTests = MatchSequence (primTestOuts primTest ++ (second snd <$> others)) tests matchOutputs
      ports <- makeConditional ("matching " ++ show (src, primTest)) parent testResult (snd <$> others)
               [("didNotMatch", didNotMatchCase testIx sumTy)
               ,("didMatch",    didMatchCase testIx (primTest, snd typedPort) remainingMatchTests sumTy)]
      case ports of
        (port:_) -> pure port
        _ -> error $ "Expected at least one output port from makeConditional: got\n  " ++ show ports

    [] -> do
      -- Reorder into `matchOutputs` order
      let ins = reorderPortTbl portTable (fst <$> matchOutputs)
      -- Need to pack inputs into a tuple before feeding them into a tag node
      ports <- makeRowTag "Success" parent 1 sumTy ins
      case ports of
        [port] -> pure port
        _ -> error "Expected one port out of tag node"
 where
  reorderPortTbl :: [(Src, TypedPort)] -> [Src] -> [TypedPort]
  reorderPortTbl portTbl = fmap (fromJust . flip lookup portTbl)

  didMatchCase :: Int -- The index to put the rebuilt thing back in the wires in case of failure
               -> (PrimTest HugrType  -- The test that just matched, for book keeping
                  ,HugrType) -- and the type of the thing it was done on,
               -> MatchSequence HugrType -- The remaining tests for further matching
               -> SumOfRows
               -> NodeId
               -> [TypedPort]
               -> Compile [TypedPort]
  didMatchCase ix (prevTest, oldTy) ms@(MatchSequence{..}) sumTy parent ins = do
    -- Remember which port a src corresponds to
    let portTable = zip (fst <$> matchInputs) ins
    didAllTestsSucceed <- compileMatchSequence parent portTable ms
    makeConditional ("all matched (" ++ show ix ++ ")") parent didAllTestsSucceed []
      [("Undo", undo)
      ,("AllMatched", allMatched)
      ]
   where
    -- All of the results from tests will be at the front of `ins`.
    undo :: NodeId
         -> [TypedPort]
         -> Compile [TypedPort]
    undo parent ins = do
      -- Test results, and the rest of the inputs
      let (refined, other) = splitAt (length (primTestOuts prevTest)) ins
      undoPort <- undoPrimTest parent refined oldTy prevTest
      -- Put it back in the right place
      let (as, bs) = splitAt ix other
      let ins = as ++ undoPort : bs
      makeRowTag "Fail_Undo" parent 0 sumTy ins

    allMatched :: NodeId -> [TypedPort] -> Compile [TypedPort]
    allMatched parent = makeRowTag "AllMatched" parent 1 sumTy

  didNotMatchCase :: Int -- The index at which to put the thing we inspected in outputs
                  -> SumOfRows
                  -> NodeId
                  -> [TypedPort]
                  -> Compile [TypedPort]
  didNotMatchCase _ _ _ [] = error "No scrutinee input in didNotMatchCase"
  didNotMatchCase ix sumTy parent (scrutinee:ins) = do
    let (as, bs) = splitAt ix ins
    -- We need to wire inputs to a `Tag0`, but bringing the tested src back to
    -- the original position
    let ins = as ++ scrutinee:bs
    makeRowTag "DidNotMatch" parent 0 sumTy ins

makeRowTag :: String -> NodeId -> Int -> SumOfRows -> [TypedPort] -> Compile [TypedPort]
makeRowTag hint parent tag sor@(SoR sumRows) ins =
  if sumRows !! tag == (snd <$> ins)
  then addNodeWithInputs (hint ++ "_Tag") (parent, OpTag (TagOp tag sumRows [("hint", hint), ("tag", show tag), ("row", show (sumRows!!tag))])) ins [compileSumOfRows sor]
  else error $ "In makeRowTag " ++ hint ++ ", Elements " ++ show (snd <$> ins) ++ " do not match tag " ++ show tag ++ " of " ++ show sumRows

getSumVariants :: HugrType -> [[HugrType]]
getSumVariants (HTSum (SU (UnitSum n))) = replicate n []
getSumVariants (HTSum (SG (GeneralSum rows))) = rows
getSumVariants ty = error $ "Expected a sum type, got " ++ show ty


-- This should only be called by the logic which creates conditionals, because
-- wires that exist in the brat graph are already going to be added at the end.
addNodeWithInputs :: String -> (NodeId, HugrOp) -> [TypedPort]
                   -> [HugrType] -- The types of the outputs
                   -> Compile [TypedPort] -- The output wires
addNodeWithInputs name op inWires outTys = do
  nodeId <- addNode name op
  for_ (zip (fst <$> inWires) (Port nodeId <$> [0..])) addEdge
  pure $ zip (Port nodeId <$> [0..]) outTys

makeConditional :: String    -- Label
                -> NodeId    -- Parent node id
                -> TypedPort -- The discriminator
                -> [TypedPort] -- Other inputs
                -> [(String, NodeId -> [TypedPort] -> Compile [TypedPort])] -- Must be ordered
                -> Compile [TypedPort]
makeConditional lbl parent discrim otherInputs cases = do
  condId <- freshNode "Conditional" parent
  let rows = getSumVariants (snd discrim)
  (outTyss_cases) <- for (zip (zip [0..] cases) rows) (\((ix, (name, f)), row) -> makeCase condId name ix (row ++ (snd <$> otherInputs)) f)
  let outTys = if allRowsEqual (fst <$> outTyss_cases)
               then fst (head outTyss_cases)
               else (error "Conditional output types didn't match")
  let condOp = OpConditional (Conditional rows (snd <$> otherInputs) outTys [("label", lbl)])
  setOp condId condOp
  s <- get
  put s {hugr = H.setFirstChildren (hugr s) condId (snd <$> outTyss_cases)}
  addEdge (fst discrim, Port condId 0)
  traverse_ addEdge (zip (fst <$> otherInputs) (Port condId <$> [1..]))
  pure $ zip (Port condId <$> [0..]) outTys
 where
  makeCase :: NodeId -> String -> Int -> [HugrType] -> (NodeId -> [TypedPort] -> Compile [TypedPort]) -> Compile ([HugrType], NodeId)
  makeCase parent name ix tys f = do
    (Ctr caseId inpId outId) <- freshNodeWithIO name parent
    setOp inpId (OpIn (InputNode tys [("source", "makeCase." ++ show ix), ("context", lbl ++ "/" ++ name), ("parent", show parent)]))
    outs <- f caseId (zipWith (\offset ty -> (Port inpId offset, ty)) [0..] tys)
    let outTys = snd <$> outs
    setOp outId (OpOut (OutputNode outTys [("source", "makeCase")]))
    for_ (zip (fst <$> outs) (Port outId <$> [0..])) addEdge
    setOp caseId (OpCase (Case (FunctionType tys outTys bratExts) [("name",lbl ++ "/" ++ name)]))
    pure (outTys, caseId)

  allRowsEqual :: [[HugrType]] -> Bool
  allRowsEqual [] = True
  allRowsEqual [_] = True
  allRowsEqual (x:xs) = all (x==) xs

compilePrimTest :: NodeId
                -> TypedPort -- The thing that we're testing
                -> PrimTest HugrType -- The test to run
                -> Compile TypedPort
compilePrimTest parent (port, ty) (PrimCtorTest c tycon unpackingNode outputs) = do
  let sumOut = HTSum (SG (GeneralSum [[ty], snd <$> outputs]))
  let sig = FunctionType [ty] [sumOut] ["BRAT"]
  testId <- addNode ("PrimCtorTest " ++ show c)
            (parent
            ,OpCustom (CustomOp
                       "BRAT"
                       ("PrimCtorTest::" ++ show tycon ++ "::" ++ show c)
                       sig
                       []))
  addEdge (port, Port testId 0)
  registerCompiled unpackingNode testId
  pure (Port testId 0, sumOut)
compilePrimTest parent port@(_, ty) (PrimLitTest tm) = do
  -- Make a Const node that holds the value we test against
  constId <- addNode "LitConst" (parent, OpConst (ConstOp (valFromSimple tm)))
  loadPort <- head <$> addNodeWithInputs "LitLoad" (parent, OpLoadConstant (LoadConstantOp ty))
                       [(Port constId 0, ty)] [ty]
  -- Connect to a test node
  let sumOut = HTSum (SG (GeneralSum [[ty], []]))
  let sig = FunctionType [ty, ty] [sumOut] ["BRAT"]
  head <$> addNodeWithInputs ("PrimLitTest " ++ show tm)
           (parent, OpCustom (CustomOp "BRAT" ("PrimLitTest::" ++ show ty) sig []))
           [port, loadPort]
           [sumOut]

constructorOp :: QualName -> QualName -> FunctionType -> HugrOp
constructorOp tycon c sig = OpCustom (CustomOp "BRAT" ("Ctor::" ++ show tycon ++ "::" ++ show c) sig [])

undoPrimTest :: NodeId
             -> [TypedPort] -- The inputs we have to put back together
             -> HugrType -- The type of the thing we're making
             -> PrimTest HugrType -- The test to undo
             -> Compile TypedPort
undoPrimTest parent inPorts outTy (PrimCtorTest c tycon _ _) = do
  let sig = FunctionType (snd <$> inPorts) [outTy] ["BRAT"]
  head <$> addNodeWithInputs
           ("UndoCtorTest " ++ show c)
           (parent, constructorOp tycon c sig)
           inPorts
           [outTy]
undoPrimTest parent inPorts outTy (PrimLitTest tm) = do
  unless (null inPorts) $ error "Unexpected inPorts"
  constId <- addNode "LitConst" (parent, OpConst (ConstOp (valFromSimple tm)))
  head <$> addNodeWithInputs "LitLoad" (parent, OpLoadConstant (LoadConstantOp outTy))
           [(Port constId 0, outTy)] [outTy]

-- Create a module and FuncDecl nodes inside it for all of the functions given as argument
compileModule :: VEnv -> NodeId
              -> Compile ()
compileModule venv moduleNode = do
  -- Prepare FuncDef nodes for all functions. Every "noun" also requires a Function
  -- to compute its value.
  bodies <- for decls (\(fnName, idNode) -> do
    (funTy, extra_call, body) <- analyseDecl idNode
    ctr@Ctr {parent} <- freshNodeWithIO (show fnName ++ "_def") moduleNode
    setOp parent (OpDefn $ FuncDefn (show fnName) funTy [])
    registerFuncDef idNode (parent, extra_call)
    pure (body ctr)
    )
  for_ bodies (\body -> do
    st <- get
    -- At the start of each function, clear out the `compiled` map - these are
    -- the nodes compiled (usable) within that function. Generally Brat-graph nodes
    -- are only reachable from one TLD, but the `Id` nodes are shared, and must have
    -- their own LoadConstant/extra-Call/etc. *within each function*.
    put st { compiled = M.empty }
    body)
 where
  -- Given the Brat-Graph Id node for the decl, work out how to compile it (later);
  -- return the type of the Hugr FuncDefn, whether said FuncDefn requires an extra Call,
  -- and the procedure for compiling the contents of the FuncDefn for execution later,
  -- *after* all such FuncDefns have been registered
  analyseDecl :: Name -> Compile (PolyFuncType, Bool, Container -> Compile ())
  analyseDecl idNode = do
    (ns, es) <- gets bratGraph
    let srcPortTys = [(srcPort, ty) | (srcPort, ty, In tgt _) <- es, tgt == idNode ]
    case srcPortTys of
      -- All top-level functions are compiled into Box-es, which should look like this:
      [(Ex input 0, _)] | Just (BratNode (Box src tgt) _ outs) <- M.lookup input ns ->
        case outs of
          [(_, VFun Braty cty)] -> do
            (inTys, outTys) <- compileSig Braty cty
            pure (PolyFuncType [] (FunctionType inTys outTys bratExts), False, flip compileBox (src, tgt))
          [(_, VFun Kerny cty)] -> do
            -- We're compiling, e.g.
            --   f :: { Qubit -o Qubit }
            --   f = { h; circ(pi) }
            -- Although this looks like a constant kernel, we'll have to compile the
            -- computation that produces this constant. We do so by making a FuncDefn
            -- that takes no arguments and produces the constant kernel graph value.
            thunkTy <- HTFunc . PolyFuncType [] . (\(ins, outs) -> FunctionType ins outs bratExts) <$> compileSig Kerny cty
            pure (funcReturning [thunkTy], True, \Ctr {parent,input,output} -> do
              setOp input (OpIn (InputNode [] [("source", "analyseDecl")]))
              setOp output (OpOut (OutputNode [thunkTy] [("source", "analyseDecl")]))
              wire <- compileKernBox parent (show input) (src, tgt) cty
              addEdge (fst wire, Port output 0))
          _ -> error "Box should have exactly one output of Thunk type"
      _ -> do -- a computation, or several values
        outs <- compilePorts srcPortTys -- note compiling already-erased types, is this right?
        pure (funcReturning outs, True, compileNoun outs (map fst srcPortTys))

  -- top-level decls that are not Prims. RHS is the brat idNode
  decls :: [(QualName, Name)]
  decls = do -- in list monad, no Compile here
            (fnName, wires) <- M.toList venv
            let (Ex idNode _) = end (fst $ head wires) -- would be better to check same for all rather than just head
            case hasPrefix ["checking","globals","decl"] idNode of
              Just _ -> pure (fnName, idNode) -- assume all ports are 0,1,2...
              Nothing -> []

  funcReturning :: [HugrType] -> PolyFuncType
  funcReturning outs = PolyFuncType [] (FunctionType [] outs bratExts)

compileNoun :: [HugrType] -> [OutPort] -> Container -> Compile ()
compileNoun outs srcPorts Ctr {parent, input, output} = do
  setOp input (OpIn (InputNode [] [("source", "compileNoun")]))
  setOp output (OpOut (OutputNode outs [("source", "compileNoun")]))
  for_ (zip [0..] srcPorts) (\(outport, Ex src srcPort) ->
    compileWithInputs parent src >>= \case
      Just nodeId -> addEdge (Port nodeId srcPort, Port output outport) $> ()
      Nothing -> pure () -- if input not compilable, leave edge missing in Hugr - or just error?
    )

compile :: Store
        -> Namespace
        -> Graph
        -> CaptureSets
        -> VEnv
        -> BS.ByteString
compile store ns g capSets venv =
  let (hugr, moduleNode) = H.newModule ns "module"
  in evalState
    (trackM "compileFunctions" *>
     compileModule venv moduleNode *>
     trackM "dumpJSON" *>
     dumpJSON
    )
    (makeCS (g, capSets, store) hugr)
