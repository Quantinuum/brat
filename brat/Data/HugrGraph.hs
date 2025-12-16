{-# LANGUAGE OverloadedStrings #-}
module Data.HugrGraph(Hugr, PortId(..),
                      newWithRoot, addOp, getParent, getOp,
                      addEdge, addOrderEdge, edgeList,
                      serialize
                     ) where

import Data.Hugr hiding (Hugr)
import qualified Data.Hugr as D
import Data.List (partition, sortBy)
import Data.Maybe (fromMaybe)
import Data.Ord (comparing)
import qualified Data.Map as M

data Hugr node = HugrGraph {
    -- the values here are (parent, op).
    -- exactly one node (the root) will have parent == self
    nodes :: M.Map node (node, HugrOp),
    edges_out :: M.Map node [(Int, PortId node)],
    edges_in :: M.Map node [(PortId node, Int)]
} deriving (Eq, Show) -- we probably want a better `show`

addOp :: Ord node => Hugr node -> node -> (node, HugrOp) -> Hugr node
-- Do not insist the parent exists, we are not there yet
addOp h@HugrGraph {nodes} name weight =
  -- alter + partial match is just to fail if key already present
  h { nodes = M.alter (\Nothing -> Just weight) name nodes }

newWithRoot :: node -> HugrOp -> Hugr node
newWithRoot name op = HugrGraph {
  nodes = M.singleton name (name, op),
  edges_in = M.empty,
  edges_out = M.empty 
}

addEdge :: Ord node => Hugr node -> (PortId node, PortId node) -> Hugr node
addEdge HugrGraph {..} (src@(Port s o), tgt@(Port t i)) = case (M.lookup s nodes, M.lookup t nodes) of
  (Just _, Just _) -> HugrGraph {
    nodes,
    edges_out = addToMap s (o, tgt) edges_out,
    edges_in = addToMap t (src, i) edges_in
   }
  _ -> error "addEdge to/from node not present"
 where
  addToMap :: Ord k => k -> v -> M.Map k [v] -> M.Map k [v]
  addToMap k v m = M.insert k (v:(fromMaybe [] $ M.lookup k m)) m

addOrderEdge :: Ord node => Hugr node -> (node, node) -> Hugr node
addOrderEdge h (src, tgt) = addEdge h (Port src orderEdgeOffset, Port tgt orderEdgeOffset)

edgeList :: Hugr node -> [(PortId node, PortId node)]
edgeList (HugrGraph {edges_out}) = [(Port n off, tgt) | (n, vs) <- M.assocs edges_out
                                                      , (off, tgt) <- vs
                                   ]

getParent :: Ord node => Hugr node -> node -> node
getParent HugrGraph {nodes} n = let (parent, _) = nodes M.! n in parent

getOp :: Ord node => Hugr node -> node -> HugrOp
getOp HugrGraph {nodes} n = let (_, op) = nodes M.! n in op

serialize :: forall node. Ord node => Hugr node -> D.Hugr Int
serialize hugr@(HugrGraph {nodes}) = D.Hugr (
    [(transNode parent, op) | (parent, op) <- snd <$> sortedNodes],
    [(Port (transNode s) o, Port (transNode t) i) | (Port s o, Port t i) <- edgeList hugr]
  ) where
    sortOrder :: (node, (node, HugrOp)) -> (HugrOp, node, node)
    sortOrder (name, (parent, op)) = (op, parent, name)
    
    sortedNodes :: [(node, (node, HugrOp))]
    sortedNodes = let isRoot (name, (parent, _op)) = name == parent
                      ([root], rest) = partition isRoot (M.assocs nodes)
                  in (root:(sortBy (comparing sortOrder) rest))

    transNode :: node -> Int
    transNode = ((M.fromList $ zip (fst <$> sortedNodes) [0..]) M.!)
