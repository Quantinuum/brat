-- TODO: Remove DFG children of case nodes. Case nodes have inputs and outputs, so they *are* the DFG
-- possibly we need to be smart about compiling DFGs for this
-- they're getting the boxes as arguments

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Brat.Compile.Hugr (compileKernel) where

import Brat.Constructors.Patterns (pattern CFalse, pattern CTrue)
import Brat.Checker.Monad (track, trackM, CheckingSig(..), CaptureSets)
import Brat.Checker.Helpers (binderToValue)
import Brat.Checker.Types (Store(..), VEnv)
import Brat.Eval (eval, evalCTy, kindType)
import Brat.Graph hiding (lookupNode)
import Brat.Naming hiding (root)
import Brat.QualName
import Brat.Syntax.Port
import Brat.Syntax.Common
import Brat.Syntax.Simple (SimpleTerm)
import Brat.Syntax.Value
import Bwd
import Control.Monad.Freer
import Data.Hugr
import Data.HugrGraph (HugrGraph(..), NodeId)
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
 , hugr :: HugrGraph
 , compiled :: M.Map Name NodeId  -- Mapping from Brat nodes to Hugr nodes
 -- When lambda lifting, captured variables become extra function inputs.
 -- This maps from the captured value (in the BRAT graph, perhaps outside the current func/lambda)
 -- to the Hugr port capturing it in the current context.
 , liftedOutPorts :: M.Map OutPort (PortId NodeId)
 , holes :: Bwd (NodeId, OutPort) -- where to splice in result of another Brat computation
 , store :: Store -- Kinds and values of global variables, for compiling types
 }

type Compile = State CompilationState

onHugr :: State HugrGraph a -> Compile a
onHugr f = get >>= \s -> let (r, h') = runState f (hugr s) in put (s {hugr=h'}) >> pure r

data Container = Ctr {
  parent :: NodeId,
  input :: NodeId,
  output :: NodeId
}

makeCS :: (Graph, Store) -> HugrGraph -> CompilationState
makeCS (g, store) hugr =
  CompilationState
    { bratGraph = g
    , hugr = hugr
    , compiled = M.empty
    , holes = B0
    , liftedOutPorts = M.empty
    , store = store
    }

freshNode :: String -> NodeId -> Compile NodeId
freshNode name parent = onHugr (H.freshNode parent name)

makeIO :: String -> NodeId -> Compile Container
makeIO name parent = do
  input <- freshNode (name ++ "_Input") parent
  output <- freshNode (name ++ "_Input") parent
  onHugr $ H.setFirstChildren parent [input, output]
  pure $ Ctr {parent, input, output}

freshNodeWithIO :: String -> NodeId -> Compile Container
freshNodeWithIO name parent = freshNode name parent >>= makeIO name

addEdge :: (PortId NodeId, PortId NodeId) -> Compile ()
addEdge e = onHugr (H.addEdge e)

addNode :: String -> (NodeId, HugrOp) -> Compile NodeId
addNode nam (parent, op) = do
  name <- freshNode nam parent
  setOp name (addMetadata [("id", show name)] op)
  pure name

-- Add a hole, record that it should be filled from the specified OutPort
addHole :: NodeId -> FunctionType -> OutPort -> Compile NodeId
addHole parent sig outPort = do
  -- hole index is not important now, we identify holes by NodeId
  hole <- gets (length . holes) -- but anyway
  h <- addNode ("hole " ++ show hole) (parent, OpCustom (holeOp hole sig))
  st <- get
  put (st { holes = (holes st) :< (h, outPort)})
  pure h

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
setOp name op = onHugr (H.setOp name op)

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

dumpJSON :: Compile BS.ByteString
dumpJSON = gets hugr <&> (encode . H.serialize)

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
      ctr@Ctr {parent=dfgId} <- freshNodeWithIO "DidMatch" parent
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
    Just _ -> error "Kernel contained call to global; should have been a splice"
    _ -> do
      (ns, _) <- gets bratGraph
      let node = ns M.! name
      trackM ("compileNode (" ++ show parent ++ ") " ++ show name ++ " " ++ show node)
      nod_edge_info <- case node of
        (BratNode _ _ _) -> error "Can't compile classical Brat"
        (KernelNode thing ins outs) -> compileNode' thing ins outs
      case nod_edge_info of
        Nothing -> pure Nothing
        Just (node, tgtOffset, extra_edges) -> do
          trans_edges <- compileInEdges parent name <&> map (second (+tgtOffset))
          pure $ Just (node, extra_edges ++ trans_edges)

  default_edges :: NodeId -> Maybe (NodeId, Int, [(PortId NodeId, Int)])
  default_edges nid = Just (nid, 0, [])

  compileNode' :: NodeType Kernel -> [(PortName, Val Z)] -> [(PortName, Val Z)]
                  -- Result is nodeid, port offset, *extra* edges
               -> Compile (Maybe (NodeId, Int, [(PortId NodeId, Int)]))
  compileNode' thing ins outs = case thing of
    Const tm -> default_edges <$> (compilePorts outs >>= (compileConst parent tm . head))
    Splice outPort@(Ex outNode _) -> default_edges <$> do
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

        Nothing -> addHole parent sig outPort

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
    Selector _c -> error "Todo: selector"
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
  onHugr $ H.setFirstChildren condId (snd <$> outTyss_cases)
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

compileKernel :: (Namespace, Store, Graph)
              -> String -> Name
              -> (BS.ByteString, [(NodeId, OutPort)])
compileKernel (nsp, store, g@(ns, es)) desc name = (hugr, holelist) where
  (src_tgt, outs) = case ns M.! name of
    (BratNode Id _ _) -> case [srcPort | (srcPort, _, In tgt _) <- es, tgt == name ] of
      -- All top-level functions are compiled into Box-es, which should look like this:
      [Ex input 0] | Just (BratNode (Box src tgt) [] outs) <- M.lookup input ns -> ((src, tgt), outs)
    (BratNode (Box src tgt) [] outs) -> ((src, tgt), outs)
    nt -> error $ "Can only compile Box nodes or Id from them, not " ++ show nt ++ " (for " ++ show name ++ ")"
  cty = case outs of
    [(_, VFun Kerny cty)] -> cty
  startHugr = H.new nsp desc (OpDFG $ DFG (FunctionType hInTys hOutTys bratExts) [])
  (hugr, holelist) = flip evalState (makeCS (g,store) startHugr) $ do
    ctr <- makeIO desc (root startHugr)
    compileBox ctr src_tgt
    json <- dumpJSON
    hs <- gets holes
    pure (json, hs <>> [])

  (hInTys, hOutTys) = runLocalChecking (evalCTy S0 Kerny cty <&> (\(ss :->> ts) -> (compileRo ss, compileRo ts)))

  runLocalChecking :: Free CheckingSig t -> t
  runLocalChecking (Ret t) = t
  runLocalChecking (Req (ELup e) k) = runLocalChecking (k (M.lookup e (valueMap store)))
  runLocalChecking (Req _ _) = error "Compile monad found a command it can't handle"
