{-# LANGUAGE OverloadedStrings #-}
module Data.HugrGraph(NodeId,
                      HugrGraph(root), -- do NOT export contents, keep abstract
                      new, splitNamespace,
                      freshNode,
                      setFirstChildren,
                      setOp, getParent, getOp,
                      addEdge, addOrderEdge,
                      edgeList, serialize
                     ) where

import Brat.Naming (Namespace, Name, fresh, split)
import Bwd
import Data.Hugr hiding (const)

import Control.Monad.State (State, execState, state)
import Data.Foldable (for_)
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
  addToMap k v m = M.alter (Just . (v:) . fromMaybe []) k m

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
