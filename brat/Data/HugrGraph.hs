{-# LANGUAGE OverloadedStrings #-}
module Data.HugrGraph(NodeId,
                      HugrGraph(root), -- do NOT export contents, keep abstract
                      new,
                      freshNode,
                      setFirstChildren,
                      setOp, getParent, getOp,
                      addEdge, addOrderEdge,
                      serialize,
                      splice, spliceNew, splicePrepend, inlineDFG
                     ) where

import Brat.Naming (Namespace, Name(..), fresh)
import Bwd
import Data.Hugr hiding (const)

import Control.Monad.State (State, execState, state, get, put, modify)
import Data.Foldable (foldl', for_)
import Data.Functor ((<&>))
import Data.Bifunctor (first)
import Data.Maybe (fromMaybe)
import qualified Data.Map as M

track = const id

newtype NodeId = NodeId Name deriving (Eq, Ord, Show)

data HugrGraph n = HugrGraph {
    root :: n,
    parents :: M.Map n n, -- definitive list of (valid) nodes, excluding root
    firstChildren:: M.Map n [n],
    nodes :: M.Map n HugrOp,
    edgesOut :: M.Map n [(Int, PortId n)],
    edgesIn :: M.Map n [(PortId n, Int)]
} deriving (Eq, Show) -- we probably want a better `show`

freshNode :: NodeId -> String -> State (HugrGraph NodeId, Namespace) NodeId
freshNode parent nam = state $ \(hugr@HugrGraph {root, parents}, nameSupply) ->
  case M.lookup parent parents of
    Nothing | parent /= root-> error "parent does not exist"
    _ -> let (freshName, newSupply) = fresh nam nameSupply
         in (NodeId freshName, (hugr {
              parents = M.alter (\Nothing -> Just parent) (NodeId freshName) parents
            }, newSupply))

-- ERRORS if firstChildren already set for this node
setFirstChildren :: Ord n => n -> [n] -> State (HugrGraph n) ()
setFirstChildren p cs = modify $ \h -> let nch = M.alter (\Nothing -> Just cs) p (firstChildren h)
                                      in h {firstChildren = nch}

-- ERRORS if op already set for this node (or node does not have parent - should not be possible)
setOp :: (Ord n, Show n) => n -> HugrOp -> State (HugrGraph n) ()
setOp name op = state $ \h@HugrGraph {parents, nodes} -> case M.lookup name parents of
  Nothing -> error $ "Node " ++ show name ++ " has no parent"
  Just _ ->
    -- alter + partial match is just to fail if key already present
    ((), h { nodes = M.alter (\Nothing -> Just op) name nodes })

-- Create a new HugrGraph with a single node (root) with specified op
new :: String -> HugrOp -> State Namespace (HugrGraph NodeId)
new nam op = state $ \ns ->
  let (name, ns') = fresh nam ns
      root = NodeId name
  in (HugrGraph {
        root,
        parents = M.empty,
        firstChildren = M.empty,
        nodes = M.singleton root op,
        edgesIn = M.empty,
        edgesOut = M.empty}
      ,ns'
      )

addEdge :: Ord n =>(PortId n, PortId n) -> State (HugrGraph n) ()
addEdge (src@(Port s o), tgt@(Port t i)) = state $ \h@HugrGraph {..} ->
  ((), ) $ case (M.lookup s nodes, M.lookup t nodes) of
    (Just _, Just _) -> h {
      edgesOut = addToMap s (o, tgt) edgesOut id,
      edgesIn = addToMap t (src, i) edgesIn no_other_inedge
    }
    _ -> error "addEdge to/from node not present"
 where
  addToMap :: Ord k => k -> v -> M.Map k [v] -> ([v] -> [v]) -> M.Map k [v]
  addToMap k v m chk = M.alter (Just . (v:) . maybe [] chk) k m
  no_other_inedge :: [(n, Int)] -> [(n, Int)]
  no_other_inedge [] = []
  no_other_inedge ((n, j):xs) | i == j = error "multiple in-edges to same port"
                           | otherwise = (n, j) : no_other_inedge xs

addOrderEdge :: Ord n => (n, n) -> State (HugrGraph n) ()
addOrderEdge (src, tgt) = addEdge (Port src orderEdgeOffset, Port tgt orderEdgeOffset)

edgeList :: HugrGraph n -> [(PortId n, PortId n)]
edgeList (HugrGraph {edgesOut}) = [(Port n off, tgt) | (n, vs) <- M.assocs edgesOut
                                                      , (off, tgt) <- vs
                                   ]

getParent :: Ord n => HugrGraph n -> n -> n
getParent HugrGraph {parents} n = parents M.! n

getOp :: Ord n => HugrGraph n -> n -> HugrOp
getOp HugrGraph {nodes} n = nodes M.! n

-- Replaces the specified node of the host Hugr (in the State monad), with a new Hugr
-- (as a subtree), given a key-translation function for any non-root key of the new Hugr
-- to a valid (unused) key in the host. (The most general form of splicing.)
-- We expect the new Hugr to be DFG-rooted with the same signature as the hole
-- being replaced, although this is not enforced.
splice :: forall m n. (Ord n, Ord m) => n -> HugrGraph m -> (m -> n) -> State (HugrGraph n) ()
splice hole add non_root_k = modify $ \host -> case M.lookup hole (nodes host) >>= isHole of
  Just (_, sig) -> case M.lookup (root add) (nodes add) of
    -- We could inline the DFG here, which could be done more efficiently (iterating through
    -- nodes of `add` but not the host), but for now we just splice in the DFG in place
    -- of the hole with its subtree beneath it.
    Just (OpDFG (DFG sig' _)) | sig == sig' -> host {
        parents = disj_union (parents host) (M.mapKeys k $ M.map k $ parents add),
        -- union prefers left --> override host `nodes` for `hole` with new (DFG)
        nodes = M.union (M.mapKeys k (nodes add)) (nodes host),
        edgesIn  = disj_union (edgesIn host) new_edgesIn,
        edgesOut = disj_union (edgesOut host) new_edgesOut,
        firstChildren = disj_union (firstChildren host)
                                    (M.mapKeys k $ M.map (k <$>) $ firstChildren add)
      }
    other -> error $ "Expected DFG with sig " ++ show sig ++ "\nBut found: " ++ show other
  other -> error $ "Expected a hole, found " ++ show other
  where
    k :: m -> n
    k n = if n == root add then hole else non_root_k n

    new_edgesIn = M.fromList [(k tgt, [(Port (k srcNode) srcPort, tgtPort)
                                       | (Port srcNode srcPort, tgtPort) <- in_edges ])
                              | (tgt, in_edges ) <- M.assocs (edgesIn add)]

    new_edgesOut = M.fromList [(k src, [(srcPort, Port (k tgtNode) tgtPort)
                                       | (srcPort, Port tgtNode tgtPort) <- out_edges])
                              | (src, out_edges) <- M.assocs (edgesOut add)]

    disj_union = M.unionWith (\_ _ -> error "keys not disjoint")

-- Replace the specified hole of the host Hugr (in the State monad), with a new Hugr,
-- where both have NodeId keys, by prefixing the new Hugr's keys with the NodeId of
-- the hole
splicePrepend :: NodeId -> HugrGraph NodeId -> State (HugrGraph NodeId) ()
splicePrepend hole add = splice hole add (keyMap M.!)
 where
  prefixRoot :: NodeId -> NodeId
  prefixRoot (NodeId (MkName ids)) = let NodeId (MkName rs) = hole in NodeId $ MkName (rs ++ ids)

  keyMap :: M.Map NodeId NodeId
  -- translate `add` keys (except `root add`) into `host` by prefixing with `hole`
  -- parent is definitive list of non-root nodes
  keyMap = M.fromList $ [(k, prefixRoot k) | k <- M.keys (parents add)]

-- Replace the specified hole of a host Hugr (in the State monad, with NodeId keys) with
-- a new Hugr of any key type, using a Namespace to generate a fresh NodeId for each node
-- of the new Hugr
spliceNew :: forall n. (Ord n, Show n) => NodeId -> HugrGraph n -> State (HugrGraph NodeId, Namespace) ()
spliceNew hole add = modify $ \(host, ns) ->
  let
   (ns_out, keyMap) = foldr newMapping (ns, M.empty) (M.keys (parents add))
   newMapping :: n -> (Namespace, M.Map n NodeId) -> (Namespace, M.Map n NodeId)
   newMapping n (ns, km) = let (nn, ns') = fresh (show n) ns in (ns', M.insert n (NodeId nn) km)
   host_out = execState (splice hole add (keyMap M.!)) host
  in (host_out, ns_out)

-- Inline a DFG node in the Hugr, i.e. make the children of the DFG become children
-- of the DFG's parent, removing the DFG and (only) its Input+Output children
inlineDFG :: Ord n => n -> State (HugrGraph n) ()
inlineDFG dfg = get >>= \h -> case M.lookup dfg (nodes h) of
  (Just (OpDFG _)) -> do
    let newp = parents h M.! dfg
    let [inp, out] = firstChildren h M.! dfg
    -- rewire edges
    dfg_in_map <- takeInEdgeMap dfg
    input_out_map <- takeOutEdges inp
    for_ input_out_map $ \(outp, dest) -> addEdge (dfg_in_map M.! outp, dest)
    dfg_out_map <- takeOutEdges dfg
    output_in_map <- takeInEdgeMap out
    for_ dfg_out_map $ \(outp, dest) -> addEdge (output_in_map M.! outp, dest)
    -- remove dfg, inp, out; reparent children of dfg
    let to_remove = [dfg, inp, out]
    modify $ \h -> h {
      firstChildren = M.delete dfg (firstChildren h), -- inp/out shouldn't have any children
      nodes = foldl (flip M.delete) (nodes h) to_remove,
      -- TODO this is O(size of hugr) reparenting. Either add a child map,
      -- or combine with splicing so we only iterate through the inserted
      -- hugr (which we do anyway) rather than the host.
      parents = M.fromList [(n, if p==dfg then newp else p)
                          | (n,p) <- M.assocs (parents h), n `notElem` to_remove]
    }
  other -> error $ "Expected DFG, found " ++ show other
 where
  takeInEdgeMap n = takeInEdges n <&> \es -> M.fromList [(p, src) | (src, p) <- es]

takeInEdges :: forall n. Ord n => n -> State (HugrGraph n) [(PortId n, Int)]
takeInEdges tgt = do
  h <- get
  let (removed_edges, edgesIn') = first (fromMaybe []) $ M.updateLookupWithKey
        (\_ _ -> Nothing) tgt (edgesIn h)
  let edgesOut' = foldl removeFromOutMap (edgesOut h) removed_edges
  put h {edgesIn=edgesIn', edgesOut=edgesOut'}
  pure removed_edges
 where
  removeFromOutMap :: M.Map n [(Int, PortId n)] -> (PortId n, Int) -> M.Map n [(Int, PortId n)]
  removeFromOutMap eos (Port src outport, inport) = M.alter (\(Just es) -> Just $ removeFromOutList es (outport, Port tgt inport)) src eos

  removeFromOutList :: [(Int, PortId n)] -> (Int, PortId n) -> [(Int, PortId n)]
  removeFromOutList [] _ = error "Out-edge not found"
  removeFromOutList (e:es) e' | e == e' = es
  removeFromOutList ((outport, _):_) (outport', _) | outport == outport' = error "Wrong out-edge"
  removeFromOutList (e:es) r = e:removeFromOutList es r

takeOutEdges :: forall n. Ord n => n -> State (HugrGraph n) [(Int, PortId n)]
takeOutEdges src = do
  h <- get
  let (removed_edges, edgesOut') = first (fromMaybe []) $ M.updateLookupWithKey
       (\_ _ -> Nothing) src (edgesOut h)
  let edgesIn' = foldl removeFromInMap (edgesIn h) removed_edges
  put h {edgesIn=edgesIn', edgesOut=edgesOut'}
  pure removed_edges
 where
  removeFromInMap :: M.Map n [(PortId n, Int)] -> (Int, PortId n) -> M.Map n [(PortId n, Int)]
  removeFromInMap eis (outport, Port tgt inport) = M.alter (\(Just es) -> Just $ removeFromInList es (Port src outport, inport)) tgt eis

  removeFromInList:: [(PortId n, Int)] -> (PortId n, Int) -> [(PortId n, Int)]
  removeFromInList [] _ = error "In-edge not found"
  removeFromInList (e:es) e' | e==e' = es
  removeFromInList ((_, inport):_) (_,inport') | inport == inport' = error "Wrong in-edge"
  removeFromInList (e:es) r = e:removeFromInList es r

serialize :: forall n. (Ord n, Show n) => HugrGraph n -> Hugr Int
serialize hugr = renameAndSort (execState (for_ orderEdges addOrderEdge) hugr)
 where
  orderEdges :: [(n, n)]
  orderEdges =
    -- Nonlocal edges (from a node to another which is a *descendant* of a sibling of the source)
    -- require an extra order edge from the source to the sibling that is ancestor of the target
    let interEdges = [(n1, n2) | (Port n1 _, Port n2 _) <- edgeList hugr,
            parentOf n1 /= parentOf n2,
            requiresOrderEdge n1,
            requiresOrderEdge n2] in
    track ("interEdges: " ++ show interEdges) (walkUp <$> interEdges)

  requiresOrderEdge :: n -> Bool
  requiresOrderEdge n = case getOp hugr n of
    OpMod _ -> False
    OpDefn _ -> False
    OpConst _ -> False
    _ -> True

  parentOf = getParent hugr

  -- Walk up the hierarchy from the tgt until we hit a node at the same level as src
  walkUp :: (n, n) -> (n, n)
  walkUp (src, tgt) | parentOf src == parentOf tgt = (src, tgt)
  walkUp (_, tgt) | parentOf tgt == tgt = error "Tgt was not descendant of Src-parent"
  walkUp (src, tgt) = walkUp (src, parentOf tgt)

-- this should be local to renameAndSort but local `type` is not allowed
type StackAndIndices n = (Bwd (n, HugrOp) -- node is index, this is (parent, op)
                         , M.Map n Int)

renameAndSort :: forall n. Ord n => HugrGraph n -> Hugr Int
renameAndSort hugr@(HugrGraph {root, firstChildren=fc, nodes, parents}) = Hugr (
    first transNode <$> fst nodeStackAndIndices <>> [],
    [(Port (transNode s) o, Port (transNode t) i) | (Port s o, Port t i) <- edgeList hugr]
  ) where
    firstChildren k = M.findWithDefault [] k fc
    nodeStackAndIndices :: StackAndIndices n
    nodeStackAndIndices = let just_root = (B0 :< (root, nodes M.! root), M.singleton root 0)
                          in foldl' addNode just_root (firstChildren root ++ M.keys parents)

    addNode :: StackAndIndices n -> n -> StackAndIndices n
    addNode ins n = case M.lookup n (snd ins) of
      (Just _) -> ins
      Nothing -> let
        parent = parents M.! n -- guaranteed as root is always in `ins`
        with_parent@(stack, indices) = addNode ins parent -- add parent first, will recurse up
       in case M.lookup n indices of
            Just _ -> with_parent -- self added by recursive call; we must be in parent's firstChildren 
            Nothing -> let with_n = (stack :< (parent, nodes M.! n), M.insert n (M.size indices) indices)
                       -- finally add firstChildren immediately after n
                       in foldl addNode with_n (firstChildren n)

    transNode :: n -> Int
    transNode = (snd nodeStackAndIndices M.!)
