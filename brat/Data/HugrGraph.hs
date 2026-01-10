{-# LANGUAGE OverloadedStrings #-}
module Data.HugrGraph(NodeId,
                      HugrGraph(root), -- do NOT export contents, keep abstract
                      new,
                      freshNode,
                      setFirstChildren,
                      setOp, getParent, getOp,
                      addEdge, addOrderEdge,
                      serialize
                     ) where

import Brat.Naming (Namespace, Name, fresh)
import Bwd
import Data.Hugr hiding (const)

import Control.Monad.State (State, execState, modify, state)
import Data.Foldable (foldl', for_)
import Data.Bifunctor (first)
import qualified Data.Map as M

track = const id

newtype NodeId = NodeId Name deriving (Eq, Ord, Show)

data HugrGraph n = HugrGraph {
    root :: n,
    parents :: M.Map n n, -- definitive list of (valid) nodes, excluding root
    first_children:: M.Map n [n],
    nodes :: M.Map n HugrOp,
    edges_out :: M.Map n [(Int, PortId n)],
    edges_in :: M.Map n [(PortId n, Int)]
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
setFirstChildren p cs = modify $ \h -> let nch = M.alter (\Nothing -> Just cs) p (first_children h)
                                      in h {first_children = nch}

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
        first_children = M.empty,
        nodes = M.singleton root op,
        edges_in = M.empty,
        edges_out = M.empty}
      ,ns'
      )

addEdge :: Ord n =>(PortId n, PortId n) -> State (HugrGraph n) ()
addEdge (src@(Port s o), tgt@(Port t i)) = state $ \h@HugrGraph {..} ->
  ((), ) $ case (M.lookup s nodes, M.lookup t nodes) of
    (Just _, Just _) -> h {
      edges_out = addToMap s (o, tgt) edges_out id,
      edges_in = addToMap t (src, i) edges_in no_other_inedge
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
edgeList (HugrGraph {edges_out}) = [(Port n off, tgt) | (n, vs) <- M.assocs edges_out
                                                      , (off, tgt) <- vs
                                   ]

getParent :: Ord n => HugrGraph n -> n -> n
getParent HugrGraph {parents} n = parents M.! n

getOp :: Ord n => HugrGraph n -> n -> HugrOp
getOp HugrGraph {nodes} n = nodes M.! n

serialize :: forall n. (Ord n, Show n) => HugrGraph n -> Hugr Int
serialize hugr = renameAndSort (execState (for_ orderEdges addOrderEdge) hugr)
 where
  orderEdges :: [(n, n)]
  orderEdges =
    -- Nonlocal edges (from a node to another which is a *descendant* of a sibling of the source)
    -- require an extra order edge from the source to the sibling that is ancestor of the target
    let interEdges = [(n1, n2) | (Port n1 _, Port n2 _) <- edgeList hugr,
            (parentOf n1 /= parentOf n2),
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

renameAndSort :: forall n . Ord n => HugrGraph n -> Hugr Int
renameAndSort hugr@(HugrGraph {root, first_children=fc, nodes, parents}) = Hugr (
    (first transNode) <$> (fst nodeStackAndIndices) <>> [],
    [(Port (transNode s) o, Port (transNode t) i) | (Port s o, Port t i) <- edgeList hugr]
  ) where
    first_children k = M.findWithDefault [] k fc
    nodeStackAndIndices :: StackAndIndices n
    nodeStackAndIndices = let just_root = (B0 :< (root, nodes M.! root), M.singleton root 0)
                          in foldl' addNode just_root (first_children root ++ M.keys parents)
    
    addNode :: StackAndIndices n -> n -> StackAndIndices n
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

    transNode :: n -> Int
    transNode = ((snd nodeStackAndIndices) M.!)
