{-# LANGUAGE OverloadedStrings #-}
module Data.HugrGraph(NodeId, PortId(..),
                      HugrGraph(root), -- do NOT export contents, keep abstract
                      new, splitNamespace,
                      freshNode,
                      setFirstChildren,
                      setOp, getParent, getOp,
                      addEdge, addOrderEdge,
                      edgeList, serialize
                     ) where

import Brat.Naming

import Bwd
import Data.Hugr

import Data.Bifunctor (first)
import Data.Maybe (fromMaybe)
import qualified Data.Map as M

newtype NodeId = NodeId Name deriving (Eq, Ord, Show)

data HugrGraph = HugrGraph {
    root :: NodeId,
    parents :: M.Map NodeId NodeId, -- definitive list of (valid) nodes, excluding root
    io_children:: M.Map NodeId (NodeId, NodeId),
    nodes :: M.Map NodeId HugrOp,
    edges_out :: M.Map NodeId [(Int, PortId NodeId)],
    edges_in :: M.Map NodeId [(PortId NodeId, Int)],
    nameSupply :: Namespace
} deriving (Eq, Show) -- we probably want a better `show`

splitNamespace :: HugrGraph -> String -> (Namespace, HugrGraph)
splitNamespace hugr n = let (nsx, nsNew) = split n (nameSupply hugr)
                        in (nsx, hugr {nameSupply = nsNew})

freshNode :: HugrGraph -> NodeId -> String -> (NodeId, HugrGraph)
freshNode hugr@(HugrGraph {root, parents, nameSupply}) parent nam =
  case M.lookup parent parents of
    Nothing | parent /= root-> error "parent does not exist"
    _ -> let (freshName, newSupply) = fresh nam nameSupply
         in (NodeId freshName, hugr {
              nameSupply = newSupply,
              parents = M.alter (\Nothing -> Just parent) (NodeId freshName) parents
            })

-- This is a hack to deal with Conditionals, whose cases must be ordered.
-- For now it only works if there are exactly two cases...
setFirstChildren :: HugrGraph -> NodeId -> [NodeId] -> HugrGraph
setFirstChildren h p [c1,c2] = h {io_children = M.alter (\Nothing -> Just (c1,c2)) p (io_children h)}

setOp :: HugrGraph -> NodeId -> HugrOp -> HugrGraph
-- Insist the parent exists
setOp h@HugrGraph {parents, nodes} name op = case M.lookup name parents of
  Nothing -> error "name has no parent"
  Just _ ->
    -- alter + partial match is just to fail if key already present
    h { nodes = M.alter (\Nothing -> Just op) name nodes }

new :: Namespace -> String -> HugrOp -> HugrGraph
new ns nam op =
  let (name, ns') = fresh nam ns
      root = NodeId name
  in HugrGraph {
        root,
        parents = M.empty,
        io_children = M.empty,
        nodes = M.singleton root op,
        edges_in = M.empty,
        edges_out = M.empty,
        nameSupply = ns'
      }

addEdge :: HugrGraph -> (PortId NodeId, PortId NodeId) -> HugrGraph
addEdge h@HugrGraph {..} (src@(Port s o), tgt@(Port t i)) = case (M.lookup s nodes, M.lookup t nodes) of
  (Just _, Just _) -> h {
    edges_out = addToMap s (o, tgt) edges_out,
    edges_in = addToMap t (src, i) edges_in
   }
  _ -> error "addEdge to/from node not present"
 where
  addToMap :: Ord k => k -> v -> M.Map k [v] -> M.Map k [v]
  addToMap k v m = M.insert k (v:(fromMaybe [] $ M.lookup k m)) m

addOrderEdge :: HugrGraph -> (NodeId, NodeId) -> HugrGraph
addOrderEdge h (src, tgt) = addEdge h (Port src orderEdgeOffset, Port tgt orderEdgeOffset)

edgeList :: HugrGraph -> [(PortId NodeId, PortId NodeId)]
edgeList (HugrGraph {edges_out}) = [(Port n off, tgt) | (n, vs) <- M.assocs edges_out
                                                      , (off, tgt) <- vs
                                   ]

getParent :: HugrGraph -> NodeId -> NodeId
getParent HugrGraph {parents} n = parents M.! n

getOp :: HugrGraph -> NodeId -> HugrOp
getOp HugrGraph {nodes} n = nodes M.! n

-- this should be local to serialize but local `type` is not allowed
type StackAndIndices = (Bwd (NodeId, HugrOp) -- node is index, this is (parent, op)
                       , M.Map NodeId Int)

serialize :: HugrGraph -> Hugr Int
serialize hugr@(HugrGraph {root, nodes, parents}) = Hugr (
    (first transNode) <$> (fst nodeStackAndIndices) <>> [],
    [(Port (transNode s) o, Port (transNode t) i) | (Port s o, Port t i) <- edgeList hugr]
  ) where

    nodeStackAndIndices :: StackAndIndices
    nodeStackAndIndices = foldl addNode
                            (B0 :< (root, nodes M.! root), M.singleton root 0)
                            (M.keys parents)
    
    addNode :: StackAndIndices -> NodeId -> StackAndIndices
    addNode ins n = case M.lookup n (snd ins) of
      (Just _) -> ins
      Nothing -> let
        parent = parents M.! n -- guaranteed as root is always in `ins`
        with_parent@(stack, indices) = addNode ins parent -- add parent first, will recurse up
       in case M.lookup n indices of
            Just _ -> with_parent -- self added by recursive call; we must be in parent's io_children 
            Nothing -> let with_n = (stack :< (parent, nodes M.! n), M.insert n (M.size indices) indices)
                       in case M.lookup n (io_children hugr) of
                         -- finally add io_children immediately after
                         (Just (inp, out)) -> addNode (addNode with_n inp) out
                         Nothing -> with_n

    transNode :: NodeId -> Int
    transNode = ((snd nodeStackAndIndices) M.!)
