module Brat.Dot (toDotString) where

import Brat.Naming
import Brat.Graph
import Brat.Syntax.Common
import Brat.Syntax.Value
import Hasochism (N(..))

import qualified Data.GraphViz as GV
import qualified Data.GraphViz.Printing as GV
import qualified Data.GraphViz.Attributes.Complete as GV

import qualified Data.Map as M
import Data.Text.Lazy (pack, unpack)
import Data.Bifunctor (first)
import Data.Graph (reachable, transposeG)
import Data.Maybe (fromJust)
import Data.Tuple.HT (snd3)


-- Wrap Name into a new type to avoid orphan instance
newtype Name' = Name' Name deriving (Eq, Ord, Show)

instance (GV.PrintDot Name') where
  unqtDot (Name' name) = GV.text . pack . show $ name
  toDot  (Name' name) =  GV.text . pack $ "\"" ++ show name ++ "\""


data EdgeType = EvalEdge | SrcEdge | GraphEdge (Val Z)

instance Show EdgeType where
  show EvalEdge = ""
  show SrcEdge = ""
  show (GraphEdge ty) = show ty


toDotString :: Graph -> String
toDotString (ns,ws) = unpack . GV.printDotGraph $ GV.graphElemsToDot params verts edges
 where
  verts :: [(Name', Node)]
  verts = first Name' <$> M.toList ns

  edges :: [(Name', Name', EdgeType)]
  edges =
    -- Normal edges
    [ (Name' v1, Name' v2, GraphEdge ty) | (Ex v1 _, ty, In v2 _) <- ws ] ++
    -- New edges denoting references in nodes
    [ edge | (x, node) <- verts, edge <- getRefEdge x node ]

  getRefEdge :: Name' -> Node -> [(Name', Name', EdgeType)]
  getRefEdge x (BratNode (Eval (Ex y _)) _ _) = [(Name' y, x, EvalEdge)]
  getRefEdge x (KernelNode (Splice (Ex y _)) _ _) = [(Name' y, x, EvalEdge)]
  getRefEdge x (BratNode (Box src _) _ _) = [(x, Name' src, SrcEdge)]
  getRefEdge _ _ = []

  -- Map all nodes in a box to the src node
  clusterMap :: M.Map Name' Name'
  clusterMap = foldr f M.empty verts
   where
    (g, toNode, toVert) = toGraph (ns, ws)
    f (_, node) m = case node of
      BratNode (Box src tgt) _ _ ->
        -- Find all nodes in the box spanned by src and tgt, i.e. all nodes
        -- reachable from src that can reach tgt
        let srcReaches = reachable g (fromJust (toVert src))
            reachesTgt = reachable (transposeG g) (fromJust (toVert tgt))
            box = Name' . snd3 . toNode <$> (srcReaches ++ reachesTgt) in
        foldr (`M.insert` Name' src) m box
      _ -> m

  -- GV.GraphVisParams vertexType vertexLabelType edgeLabelType clusterType clusterLabelType
  params :: GV.GraphvizParams Name' Node EdgeType Name' Node
  params = GV.defaultParams {
    GV.fmtNode = \(Name' name, node) -> [
      GV.textLabel (pack $ show name ++ ":\\n" ++ showNodeType node),
      GV.Color $ GV.toColorList [ color node ],
      GV.Shape GV.BoxShape
    ],
    GV.fmtEdge = \(_, _, label) -> [
      -- It looks better of we add two spaces before label to move it
      -- a bit to the right
      GV.textLabel (pack $ "  " ++ show label),
      GV.Style [style label],
      GV.arrowTo (arrow label)
    ],
    GV.clusterBy = \n@(name, _) -> case clusterMap M.!? name of
        Just parent -> GV.C parent $ GV.N n
        Nothing -> GV.N n,
    GV.clusterID = \(Name' name) -> GV.Str (pack $ show name)
  }

  showNodeType :: Node -> String
  showNodeType (BratNode thing _ _) = show thing
  showNodeType (KernelNode thing _ _) = show thing

  color BratNode {} = GV.RGB 255 0 0
  color KernelNode {} = GV.RGB 0 0 255

  style (GraphEdge _) = GV.solid
  style _ = GV.dashed

  arrow EvalEdge = GV.oDot
  arrow _ = GV.vee
