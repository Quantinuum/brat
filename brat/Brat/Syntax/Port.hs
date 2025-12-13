module Brat.Syntax.Port where

import Brat.Naming (Name)

type PortName = String

data OutPort = Ex Name Int deriving (Eq, Ord, Show)
data InPort = In Name Int deriving (Eq, Ord, Show)

data NamedPort e = NamedPort {end :: e
                             ,portName :: PortName
                             } deriving (Show, Functor)

instance (Eq e) => Eq (NamedPort e) where
  (NamedPort {end=e1}) == NamedPort {end=e2} = e1 == e2

type Src = NamedPort OutPort
type Tgt = NamedPort InPort

class Connector t where
  getNode :: t -> Name

instance Connector OutPort where
  getNode (Ex name _) = name

instance Connector InPort where
  getNode (In name _) = name

class ToEnd t where
  toEnd :: t -> End

instance ToEnd Src where
  toEnd = ExEnd . end

instance ToEnd Tgt where
  toEnd = InEnd . end

instance ToEnd InPort where
  toEnd = InEnd

instance ToEnd OutPort where
  toEnd = ExEnd

-- N.B. Ord is derived with In < Ex
data End = InEnd InPort | ExEnd OutPort
 deriving (Eq, Ord)

instance Show End where
  show (InEnd e) = show e
  show (ExEnd e) = show e

endName :: End -> Name
endName (InEnd (In n _)) = n
endName (ExEnd (Ex n _)) = n
