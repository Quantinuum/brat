{-# LANGUAGE OverloadedStrings #-}
module Data.HugrGraph(NodeId, PortId(..), Container(..),
                      Hugr, -- do NOT export contents, keep abstract
                      newWithIO, newModule, splitNamespace,
                      freshNode, freshNodeWithIO,
                      setOp, getParent, getOp,
                      addEdge, addOrderEdge,
                      edgeList, serialize
                     ) where

import Brat.Naming

import Data.Hugr hiding (Hugr)
import qualified Data.Hugr as D
import Data.List (sortBy)
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
    root :: NodeId,
    parents :: M.Map NodeId NodeId, -- definitive list of (valid) nodes, excluding root
    io_children:: M.Map NodeId (NodeId, NodeId),
    nodes :: M.Map NodeId HugrOp,
    edges_out :: M.Map NodeId [(Int, PortId NodeId)],
    edges_in :: M.Map NodeId [(PortId NodeId, Int)],
    nameSupply :: Namespace
} deriving (Eq, Show) -- we probably want a better `show`

splitNamespace :: Hugr -> String -> (Namespace, Hugr)
splitNamespace hugr n = let (nsx, nsNew) = split n (nameSupply hugr)
                        in (nsx, hugr {nameSupply = nsNew})

freshNode :: Hugr -> NodeId -> String -> (NodeId, Hugr)
freshNode hugr@(HugrGraph {root, parents, nameSupply}) parent nam =
  case M.lookup parent parents of
    Nothing | parent /= root-> error "parent does not exist"
    _ -> let (freshName, newSupply) = fresh nam nameSupply
         in (NodeId freshName, hugr {
              nameSupply = newSupply,
              parents = M.alter (\Nothing -> Just parent) (NodeId freshName) parents
            })

freshNodeWithIO :: Hugr -> NodeId -> String -> (Container, Hugr)
freshNodeWithIO h gparent desc =
  let (parent, h2) = freshNode h gparent desc
      (input, h3) = freshNode h2 parent (desc ++ "_Input")
      (output, h4) = freshNode h3 parent (desc ++ "_Output")
  in (Ctr {parent, input, output}, h4 {io_children = M.insert parent (input, output) (io_children h4) })

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
      (inp, ns2) = fresh (nam ++ "_Input") ns1
      (outp, ns3) = fresh (nam ++ "_Output") ns2
      (root, input, output) = (NodeId name, NodeId inp, NodeId outp)
  in (HugrGraph {
        root,
        parents = M.fromList ((, root) <$> [input, output]),
        io_children = M.singleton root (input, output),
        nodes = M.singleton root op,
        edges_in = M.empty,
        edges_out = M.empty,
        nameSupply = ns3
      }
     ,Ctr {parent=root, input, output}
     )

newModule :: Namespace -> String -> (Hugr, NodeId)
newModule ns nam =
  let (name, ns') = fresh nam ns
      root = NodeId name
  in (HugrGraph {
        root,
        parents = M.empty,
        io_children = M.empty,
        nodes = M.singleton root (OpMod ModuleOp),
        edges_in = M.empty,
        edges_out = M.empty,
        nameSupply = ns'
      }
     , root
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
serialize hugr@(HugrGraph {root, nodes, parents}) = D.Hugr (
    [(transNode parent, op) | (op, parent) <- snd <$> sortedNodes],
    [(Port (transNode s) o, Port (transNode t) i) | (Port s o, Port t i) <- edgeList hugr]
  ) where
    sortedNodes :: [(NodeId, (HugrOp, NodeId))] -- name, (op, parent)
    sortedNodes = let withOp (name, parent) = (name, (nodes M.! name, parent))
                  in (withOp (root, root)):(sortBy (comparing swap) (withOp <$> M.assocs parents))

    transNode :: NodeId -> Int
    transNode = ((M.fromList $ zip (fst <$> sortedNodes) [0..]) M.!)
