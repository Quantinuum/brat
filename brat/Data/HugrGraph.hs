{-# LANGUAGE OverloadedStrings #-}
module Data.HugrGraph(NodeId,
                      HugrGraph(root), -- do NOT export contents, keep abstract
                      new, splitNamespace,
                      freshNode,
                      setFirstChildren,
                      setOp, getParent, getOp,
                      addEdge, addOrderEdge, edgeList,
                      splice, inlineDFG,
                      serialize
                     ) where

import Brat.Naming (Namespace, Name(..), fresh, split)
import Bwd
import Data.Hugr hiding (const)

import Control.Monad.State (State, execState, state, get, put, modify)
import Data.Foldable (for_)
import Data.Functor ((<&>))
import Data.Bifunctor (first)
import Data.Maybe (fromMaybe)
import qualified Data.Map as M

track = const id

newtype NodeId = NodeId Name deriving (Eq, Ord, Show)

data HugrGraph = HugrGraph {
    root :: NodeId,
    parents :: M.Map NodeId NodeId, -- definitive list of (valid) nodes, excluding root
    first_children:: M.Map NodeId [NodeId],
    nodes :: M.Map NodeId HugrOp,
    edges_out :: M.Map NodeId [(Int, PortId NodeId)],
    edges_in :: M.Map NodeId [(PortId NodeId, Int)],
    nameSupply :: Namespace
} deriving (Eq, Show) -- we probably want a better `show`

splitNamespace :: String -> State HugrGraph Namespace
splitNamespace n = state $ \hugr -> let (nsx, nsNew) = split n (nameSupply hugr)
                                    in (nsx, hugr {nameSupply = nsNew})

freshNode :: NodeId -> String -> State HugrGraph NodeId
freshNode parent nam = state $ \hugr@(HugrGraph {root, parents, nameSupply}) ->
  case M.lookup parent parents of
    Nothing | parent /= root-> error "parent does not exist"
    _ -> let (freshName, newSupply) = fresh nam nameSupply
         in (NodeId freshName, hugr {
              nameSupply = newSupply,
              parents = M.alter (\Nothing -> Just parent) (NodeId freshName) parents
            })

setFirstChildren :: NodeId -> [NodeId] -> State HugrGraph ()
setFirstChildren p cs = state $ \h -> let nch = M.alter (\Nothing -> Just cs) p (first_children h)
                                      in ((), h {first_children = nch})

setOp :: NodeId -> HugrOp -> State HugrGraph ()
-- Insist the parent exists
setOp name op = state $ \h@HugrGraph {parents, nodes} -> case M.lookup name parents of
  Nothing -> error "name has no parent"
  Just _ ->
    -- alter + partial match is just to fail if key already present
    ((), h { nodes = M.alter (\Nothing -> Just op) name nodes })

new :: Namespace -> String -> HugrOp -> HugrGraph
new ns nam op =
  let (name, ns') = fresh nam ns
      root = NodeId name
  in HugrGraph {
        root,
        parents = M.empty,
        first_children = M.empty,
        nodes = M.singleton root op,
        edges_in = M.empty,
        edges_out = M.empty,
        nameSupply = ns'
      }

addEdge :: (PortId NodeId, PortId NodeId) -> State HugrGraph ()
addEdge (src@(Port s o), tgt@(Port t i)) = state $ \h@HugrGraph {..} ->
  ((), ) $ case (M.lookup s nodes, M.lookup t nodes) of
    (Just _, Just _) -> h {
      edges_out = addToMap s (o, tgt) edges_out,
      edges_in = addToMap t (src, i) edges_in
    }
    _ -> error "addEdge to/from node not present"
 where
  addToMap :: Ord k => k -> v -> M.Map k [v] -> M.Map k [v]
  addToMap k v m = M.insert k (v:(fromMaybe [] $ M.lookup k m)) m

addOrderEdge :: (NodeId, NodeId) -> State HugrGraph ()
addOrderEdge (src, tgt) = addEdge (Port src orderEdgeOffset, Port tgt orderEdgeOffset)

edgeList :: HugrGraph -> [(PortId NodeId, PortId NodeId)]
edgeList (HugrGraph {edges_out}) = [(Port n off, tgt) | (n, vs) <- M.assocs edges_out
                                                      , (off, tgt) <- vs
                                   ]

getParent :: HugrGraph -> NodeId -> NodeId
getParent HugrGraph {parents} n = parents M.! n

getOp :: HugrGraph -> NodeId -> HugrOp
getOp HugrGraph {nodes} n = nodes M.! n

--- Replaces the specified node of the first Hugr, with the second Hugr.
splice :: HugrGraph -> NodeId -> HugrGraph -> HugrGraph
splice host hole add = case (M.lookup hole (nodes host) >>= isHole) of
  Just (_, sig) -> case M.lookup (root add) (nodes add) of
    Just (OpDFG (DFG sig' _)) | sig == sig' -> {-inlineDFG hole-} host {
        -- prefer host entry for parent of (`hole` == root of `add`)
        parents = union (parents host) (M.mapKeys k $ M.map k $ parents add),
        -- override host `nodes` for `hole` with new (DFG)
        nodes = M.union (M.mapKeys k (nodes add)) (nodes host),
        edges_in  = union (edges_in host)  $ M.fromList [(k tgt, [(Port (k srcNode) srcPort, tgtPort)
                                                                 | (Port srcNode srcPort, tgtPort) <- in_edges ])
                                                        | (tgt, in_edges ) <- M.assocs (edges_in add)],
        edges_out = union (edges_out host) $ M.fromList [(k src, [(srcPort, Port (k tgtNode) tgtPort)
                                                                 | (srcPort, Port tgtNode tgtPort) <- out_edges])
                                                        | (src, out_edges) <- M.assocs (edges_out add)],
        first_children = union (first_children host) (M.mapKeys k $ M.map (k <$>) $ first_children add)
      }
    other -> error $ "Expected DFG with sig " ++ show sig ++ "\nBut found: " ++ show other
  other -> error $ "Expected a hole, found " ++ show other
  where
    prefixRoot :: NodeId -> NodeId
    prefixRoot (NodeId (MkName ids)) = let NodeId (MkName rs) = hole in NodeId $ MkName (rs ++ ids)

    keyMap :: M.Map NodeId NodeId -- translate `add` keys into `host` by prefixing with `hole`.
    -- parent is definitive list of non-root nodes
    keyMap = M.fromList $ (root add, hole):[(k, prefixRoot k) | k <- M.keys (parents add)]

    union = M.unionWith (\_ _ -> error "keys not disjoint")
    k = (keyMap M.!)

inlineDFG :: NodeId -> State HugrGraph ()
inlineDFG dfg = get >>= \h -> case M.lookup dfg (nodes h) of
  (Just (OpDFG _)) -> do
    let newp = (parents h) M.! dfg
    let [inp, out] = (first_children h) M.! dfg
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
      first_children = M.delete dfg (first_children h), -- inp/out shouldn't have any children
      nodes = foldl (flip M.delete) (nodes h) to_remove,
      -- TODO this is O(size of hugr) reparenting. Either add a child map,
      -- or combine with splicing so we only iterate through the inserted
      -- hugr (which we do anyway) rather than the host.
      parents = M.fromList [(n, if p==dfg then newp else p)
                          | (n,p) <- M.assocs (parents h), not (elem n to_remove)]
    }
  other -> error $ "Expected DFG, found " ++ show other
 where
  takeInEdgeMap n = takeInEdges n <&> \es -> M.fromList [(p, src) | (src, p) <- es]

takeInEdges :: NodeId -> State HugrGraph [(PortId NodeId, Int)]
takeInEdges tgt = do
  h <- get
  let (removed_edges, edges_in') = first (fromMaybe []) $ M.updateLookupWithKey
        (\_ _ -> Nothing) tgt (edges_in h)
  let edges_out' = foldl removeFromOutMap (edges_out h) removed_edges
  put h {edges_in=edges_in', edges_out=edges_out'}
  pure removed_edges
 where
  removeFromOutMap :: M.Map NodeId [(Int, PortId NodeId)] -> (PortId NodeId, Int) -> M.Map NodeId [(Int, PortId NodeId)]
  removeFromOutMap eos (Port src outport, inport) = M.alter (\(Just es) -> Just $ removeFromOutList es (outport, Port tgt inport)) src eos

  removeFromOutList :: [(Int, PortId NodeId)] -> (Int, PortId NodeId) -> [(Int, PortId NodeId)]
  removeFromOutList [] _ = error "Out-edge not found"
  removeFromOutList (e:es) e' | e == e' = es
  removeFromOutList ((outport, _):_) (outport', _) | outport == outport' = error "Wrong out-edge"
  removeFromOutList (e:es) r = e:(removeFromOutList es r)

takeOutEdges :: NodeId -> State HugrGraph [(Int, PortId NodeId)]
takeOutEdges src = do
  h <- get
  let (removed_edges, edges_out') = first (fromMaybe []) $ M.updateLookupWithKey
       (\_ _ -> Nothing) src (edges_out h)
  let edges_in' = foldl removeFromInMap (edges_in h) removed_edges
  put h {edges_in=edges_in', edges_out=edges_out'}
  pure removed_edges
 where
  removeFromInMap :: M.Map NodeId [(PortId NodeId, Int)] -> (Int, PortId NodeId) -> M.Map NodeId [(PortId NodeId, Int)]
  removeFromInMap eis (outport, Port tgt inport) = M.alter (\(Just es) -> Just $ removeFromInList es (Port src outport, inport)) tgt eis

  removeFromInList:: [(PortId NodeId, Int)] -> (PortId NodeId, Int) -> [(PortId NodeId, Int)]
  removeFromInList [] _ = error "In-edge not found"
  removeFromInList (e:es) e' | e==e' = es
  removeFromInList ((_, inport):_) (_,inport') | inport == inport' = error "Wrong in-edge"
  removeFromInList (e:es) r = e:(removeFromInList es r)

serialize :: HugrGraph -> Hugr Int
serialize hugr = renameAndSort (execState (for_ orderEdges addOrderEdge) hugr)
 where
  orderEdges :: [(NodeId, NodeId)]
  orderEdges =
    -- Nonlocal edges (from a node to another which is a *descendant* of a sibling of the source)
    -- require an extra order edge from the source to the sibling that is ancestor of the target
    let interEdges = [(n1, n2) | (Port n1 _, Port n2 _) <- edgeList hugr,
            (parentOf n1 /= parentOf n2),
            requiresOrderEdge n1,
            requiresOrderEdge n2] in
    track ("interEdges: " ++ show interEdges) (walkUp <$> interEdges)

  requiresOrderEdge :: NodeId -> Bool
  requiresOrderEdge n = case getOp hugr n of
    OpMod _ -> False
    OpDefn _ -> False
    OpConst _ -> False
    _ -> True

  parentOf = getParent hugr

  -- Walk up the hierarchy from the tgt until we hit a node at the same level as src
  walkUp :: (NodeId, NodeId) -> (NodeId, NodeId)
  walkUp (src, tgt) | parentOf src == parentOf tgt = (src, tgt)
  walkUp (_, tgt) | parentOf tgt == tgt = error "Tgt was not descendant of Src-parent"
  walkUp (src, tgt) = walkUp (src, parentOf tgt)

-- this should be local to renameAndSort but local `type` is not allowed
type StackAndIndices = (Bwd (NodeId, HugrOp) -- node is index, this is (parent, op)
                       , M.Map NodeId Int)

renameAndSort :: HugrGraph -> Hugr Int
renameAndSort hugr@(HugrGraph {root, first_children=fc, nodes, parents}) = Hugr (
    (first transNode) <$> (fst nodeStackAndIndices) <>> [],
    [(Port (transNode s) o, Port (transNode t) i) | (Port s o, Port t i) <- edgeList hugr]
  ) where
    first_children k = M.findWithDefault [] k fc
    nodeStackAndIndices :: StackAndIndices
    nodeStackAndIndices = let just_root = (B0 :< (root, nodes M.! root), M.singleton root 0)
                              init = foldl addNode just_root (first_children root)
                          in foldl addNode init (M.keys parents)

    addNode :: StackAndIndices -> NodeId -> StackAndIndices
    addNode ins n = case M.lookup n (snd ins) of
      (Just _) -> ins
      Nothing -> let
        parent = parents M.! n -- guaranteed as root is always in `ins`
        with_parent@(stack, indices) = addNode ins parent -- add parent first, will recurse up
       in case M.lookup n indices of
            Just _ -> with_parent -- self added by recursive call; we must be in parent's first_children 
            Nothing -> let with_n = (stack :< (parent, nodes M.! n), M.insert n (M.size indices) indices)
                       -- finally add first_children immediately after n
                       in foldl addNode with_n (first_children n)

    transNode :: NodeId -> Int
    transNode = ((snd nodeStackAndIndices) M.!)
