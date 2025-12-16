{-# LANGUAGE OverloadedStrings #-}
module Data.HugrGraph(Hugr, NodeId, PortId(..),
                      newWithRoot, splitNamespace, rootNode,
                      freshNodeWithParent, setOp, getParent, getOp,
                      addEdge, addOrderEdge,
                      edgeList, toNodesEdges
                     ) where

import Brat.Naming

import Data.Aeson
import Data.Hugr hiding (Hugr)
import qualified Data.Hugr as D
import Data.List (partition)
import Data.Maybe (fromMaybe)
import qualified Data.Map as M
import Data.Text (Text)

newtype NodeId = NodeId Name deriving (Eq, Ord, Show)

data Hugr = HugrGraph {
    -- exactly one node (the root) will have parent == self
    parents :: M.Map NodeId NodeId,
    nodes :: M.Map NodeId HugrOp,
    edges_out :: M.Map NodeId [(Int, PortId NodeId)],
    edges_in :: M.Map NodeId [(PortId NodeId, Int)],
    nameSupply :: Namespace
} deriving (Eq, Show) -- we probably want a better `show`

-- Quite inefficient on arbitrary Hugr but used only when we know there are few nodes
rootNode :: Hugr -> NodeId
rootNode HugrGraph {parents} = let [root] = [node | (node,parent) <- M.assocs parents, node == parent]
                           in root

splitNamespace :: Hugr -> String -> (Namespace, Hugr)
splitNamespace hugr n = let (nsx, nsNew) = split n (nameSupply hugr)
                        in (nsx, hugr {nameSupply = nsNew})

freshNodeWithParent :: Hugr -> NodeId -> String -> (NodeId, Hugr)
freshNodeWithParent hugr@(HugrGraph {parents, nameSupply}) parent nam =
  case M.lookup parent parents of
    Nothing -> error "parent does not exist"
    Just _ -> let (freshName, newSupply) = fresh nam nameSupply
              in (NodeId freshName, hugr {
                nameSupply = newSupply,
                parents = M.alter (\Nothing -> Just parent) (NodeId freshName) parents
                })

setOp :: Hugr -> NodeId -> HugrOp -> Hugr
-- Insist the parent exists
setOp h@HugrGraph {parents, nodes} name op = case M.lookup name parents of
  Nothing -> error "name has no parent"
  Just _ ->
    -- alter + partial match is just to fail if key already present
    h { nodes = M.alter (\Nothing -> Just op) name nodes }

newWithRoot :: Namespace -> String -> HugrOp -> (Hugr, NodeId)
newWithRoot ns nam op =
  let (name, ns') = fresh nam ns
      node = NodeId name
  in (HugrGraph {
        parents = M.singleton node node,
        nodes = M.singleton node op,
        edges_in = M.empty,
        edges_out = M.empty,
        nameSupply = ns'
      }
     ,node
     )

addEdge :: Hugr -> (PortId NodeId, PortId NodeId) -> Hugr
addEdge h@HugrGraph {..} (src@(Port s o), tgt@(Port t i)) = case (M.lookup s nodes, M.lookup t nodes) of
  (Just _, Just _) -> h {
    edges_out = addToMap s (o, tgt) edges_out,
    edges_in = addToMap t (src, i) edges_in
   }
  _ -> error "addEdge to/from node not present"
 where
  addToMap :: Ord k => k -> v -> M.Map k [v] -> M.Map k [v]
  addToMap k v m = M.insert k (v:(fromMaybe [] $ M.lookup k m)) m

addOrderEdge :: Hugr -> (NodeId, NodeId) -> Hugr
addOrderEdge h (src, tgt) = addEdge h (Port src orderEdgeOffset, Port tgt orderEdgeOffset)

edgeList :: Hugr -> [(PortId NodeId, PortId NodeId)]
edgeList (HugrGraph {edges_out}) = [(Port n off, tgt) | (n, vs) <- M.assocs edges_out
                                                      , (off, tgt) <- vs
                                   ]

getParent :: Hugr -> NodeId -> NodeId
getParent HugrGraph {parents} n = parents M.! n

getOp :: Hugr -> NodeId -> HugrOp
getOp HugrGraph {nodes} n = nodes M.! n

toNodesEdges :: Hugr -> D.Hugr Int
toNodesEdges hugr@(HugrGraph {nodes, parents}) = D.Hugr (
    [(keyMap M.! parent, nodes M.! node) | (node, parent) <- M.assocs parents],
    [(Port (keyMap M.! s) o, Port (keyMap M.! t) i) | (Port s o, Port t i) <- edgeList hugr]
  ) where
    keyMap :: M.Map NodeId Int
    keyMap = let ([root], rest) = partition (\(name, parent) -> name == parent)
                                            (M.assocs parents)
                  -- TODO need to sort `rest` so Input/Output nodes first
             in M.fromList (zip (map fst (root:rest)) [0..])
