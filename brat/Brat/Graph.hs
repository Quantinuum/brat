{-# LANGUAGE UndecidableInstances #-}

module Brat.Graph where

import Brat.Naming
import Brat.QualName
import Brat.Syntax.Common
import Brat.Syntax.Simple
import Brat.Syntax.Value

import Hasochism (N(..))

import qualified Data.Graph as G
import qualified Data.Map as M
import Data.List.NonEmpty (NonEmpty)
import Data.Kind (Type)

data Node
  -- Inputs first, then outputs
  = BratNode (NodeType Brat) [(PortName, Val Z)] [(PortName, Val Z)]
  | KernelNode (NodeType Kernel) [(PortName, Val Z)] [(PortName, Val Z)]
 deriving Show

nodeIns :: Node -> [(PortName, Val Z)]
nodeIns (BratNode _ ins _) = ins
nodeIns (KernelNode _ ins _) = ins

nodeOuts :: Node -> [(PortName, Val Z)]
nodeOuts (BratNode _ _ outs) = outs
nodeOuts (KernelNode _ _ outs) = outs

data NodeType :: Mode -> Type where
  Prim  :: (String, String) -> NodeType Brat  -- Something external
  Const :: SimpleTerm -> NodeType a
  Eval  :: OutPort -> NodeType Brat   -- A computation on a wire
  Splice :: OutPort -> NodeType Kernel  -- A computation (classical) to add to this kernel
  Box :: Name -- Source node
      -> Name -- Target node
      -> NodeType Brat -- Graph in a box
  Source :: NodeType a  -- For building..
  Target :: NodeType a  -- ..boxes
  Id     :: NodeType a  -- Identity node for convenient wiring
  PatternMatch :: NonEmpty
                  ( TestMatchData a  -- pattern match LHS as conjunctive sequence
                  , Name  -- The node for the RHS box
                  )
               -> NodeType a
  Hypo :: NodeType a  -- Hypothesis for type checking
  Constructor :: QualName -> NodeType a
  Selector :: QualName -> NodeType a -- TODO: Get rid of this in favour of pattern matching
  ArithNode :: ArithOp -> NodeType Brat
  Replicate :: NodeType Brat
  MapFun :: NodeType a

deriving instance Show (NodeType a)

-- TestMatch nodes take the function's input row as inputs and yield one
-- output, namely a value in a sum type
-- tag 0 with the function's inputs returned as they were
-- tag 1 with the environment of pattern variables from a successful
data TestMatchData (m :: Mode) where
  TestMatchData :: Show (BinderType m) => Modey m -> MatchSequence (BinderType m) -> TestMatchData m

deriving instance Show (TestMatchData a)

-- A collections of tests to determine if a clause matches.
-- Invariants:
--    1. Each src in `matchTests` has been mentioned earlier (either in `matchInputs`
--       or in the srcs outputted by a previous `PrimCtorTest`
--    2. The same goes for the sources in `matchOutputs`
data MatchSequence ty = MatchSequence
  { matchInputs :: [(Src, ty)]
  , matchTests :: [(Src, PrimTest ty)]
  , matchOutputs ::[(Src, ty)]
  } deriving (Foldable, Functor, Traversable)
deriving instance Show ty => Show (MatchSequence ty)

data PrimTest ty
  = PrimCtorTest
      QualName      -- the data constructor
      QualName      -- the type constructor
      -- (CtorArgs m)  -- (hope we don't need) its entry in the constructor table
      Name          -- the name of the node which "outputs" the data packed inside
      [(Src, ty)]  -- ...these sources for extracted data descend
  | PrimLitTest
      SimpleTerm    -- the literal against which we're testing for equality
 deriving (Foldable, Functor, Traversable)
deriving instance Show ty => Show (PrimTest ty)

primTestOuts :: PrimTest ty -> [(Src, ty)]
primTestOuts (PrimCtorTest _ _ _ xs) = xs
primTestOuts (PrimLitTest _) = []

type Graph = (M.Map Name Node, [Wire])
emptyGraph :: Graph
emptyGraph = (M.empty, [])

instance {-# OVERLAPPING #-} Show Graph where
  show (ns, ws) = unlines (("Nodes:":(show <$> M.toList ns)) ++ ("":"Wires:":(show <$> ws)))

type Wire = (OutPort, Val Z, InPort)

toGraph :: Graph -> (G.Graph, G.Vertex -> (Node, Name, [Name]), Name -> Maybe G.Vertex)
toGraph (ns, ws) = G.graphFromEdges adj
 where
  -- TODO: Reduce the complexity (O(n^2)) of this function
  adj = [ (node
          ,name
          ,[ tgt | (Ex src _, _, In tgt _) <- ws, src == name ]
          )
        | (name, node) <- M.toList ns]

wiresFrom :: Name -> Graph -> [Wire]
wiresFrom src (_, ws) = [ w | w@(Ex a _, _, _) <- ws, a == src ]

lookupNode :: Name -> Graph -> Maybe Node
lookupNode name (ns, _) = M.lookup name ns

wireStart :: Wire -> Name
wireStart (Ex x _, _, _) = x

wireEnd :: Wire -> Name
wireEnd (_, _, In x _) = x
