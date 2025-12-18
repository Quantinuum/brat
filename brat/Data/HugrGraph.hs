{-# LANGUAGE OverloadedStrings #-}
module Data.HugrGraph(NodeId, PortId(..), Container(..),
                      Hugr, -- do NOT export contents, keep abstract
                      newWithIO, newModule, splitNamespace, rootNode,
                      freshNode, freshNodeWithIO,
                      setOp, getParent, getOp,
                      addEdge, addOrderEdge,
                      edgeList, serialize
                     ) where

import Brat.Naming

import Data.Hugr hiding (Hugr)
import qualified Data.Hugr as D
import Data.List (partition, sortBy)
import Data.Maybe (fromMaybe)
import Data.Ord (comparing)
import Data.Tuple (swap)
import qualified Data.Map as M

newtype NodeId = NodeId Name deriving (Eq, Ord, Show)

data Container = Ctr {
  parent :: NodeId,
  input :: NodeId,
  output :: NodeId
}

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

freshNode :: Hugr -> NodeId -> String -> (NodeId, Hugr)
freshNode hugr@(HugrGraph {parents, nameSupply}) parent nam =
  case M.lookup parent parents of
    Nothing -> error "parent does not exist"
    Just _ -> let (freshName, newSupply) = fresh nam nameSupply
              in (NodeId freshName, hugr {
                nameSupply = newSupply,
                parents = M.alter (\Nothing -> Just parent) (NodeId freshName) parents
                })

freshNodeWithIO :: Hugr -> NodeId -> String -> (Container, Hugr)
freshNodeWithIO h gparent desc =
  let (parent, h2) = freshNode h gparent desc
      (input, h3) = freshNode h2 parent (desc ++ "_Input")
      (output, h4) = freshNode h3 parent (desc ++ "_Output")
  in (Ctr {parent, input, output}, h4)

setOp :: Hugr -> NodeId -> HugrOp -> Hugr
-- Insist the parent exists
setOp h@HugrGraph {parents, nodes} name op = case M.lookup name parents of
  Nothing -> error "name has no parent"
  Just _ ->
    -- alter + partial match is just to fail if key already present
    h { nodes = M.alter (\Nothing -> Just op) name nodes }

newWithIO :: Namespace -> String -> HugrOp -> (Hugr, Container)
newWithIO ns nam op =
  let (name, ns1) = fresh nam ns
      (input, ns2) = fresh (nam ++ "_Input") ns1
      (output, ns3) = fresh (nam ++ "_Output") ns2
      node = NodeId name
  in (HugrGraph {
        parents = M.fromList ((, node) <$> [node, NodeId input, NodeId output]),
        nodes = M.singleton node op,
        edges_in = M.empty,
        edges_out = M.empty,
        nameSupply = ns3
      }
     ,Ctr node (NodeId input) (NodeId output)
     )

newModule :: Namespace -> String -> (Hugr, NodeId)
newModule ns nam =
  let (name, ns') = fresh nam ns
      node = NodeId name
  in (HugrGraph {
        parents = M.singleton node node,
        nodes = M.singleton node (OpMod ModuleOp),
        edges_in = M.empty,
        edges_out = M.empty,
        nameSupply = ns'
      }
     , node
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

serialize :: Hugr -> D.Hugr Int
serialize hugr@(HugrGraph {nodes, parents}) = D.Hugr (
    [(transNode parent, op) | (op, parent) <- snd <$> sortedNodes],
    [(Port (transNode s) o, Port (transNode t) i) | (Port s o, Port t i) <- edgeList hugr]
  ) where
    sortedNodes :: [(NodeId, (HugrOp, NodeId))] -- name, (op, parent)
    sortedNodes = let nodesWithParents = [(name, (nodes M.! name, parent)) | (name, parent) <- M.assocs parents]
                      isRoot (name, (_op, parent)) = name == parent
                      ([root], rest) = partition isRoot nodesWithParents
                  in root:(sortBy (comparing swap) rest)

    transNode :: NodeId -> Int
    transNode = ((M.fromList $ zip (fst <$> sortedNodes) [0..]) M.!)
