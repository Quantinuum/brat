module Data.Hugr.Extension where

import Data.Hugr (FunctionType, TypeArg, CustomOp(..), Metadata)

class OpDef t where
  signature :: t -> [TypeArg] -> FunctionType
  opName :: t -> String
  ext :: t -> String

makeOp :: OpDef t => t -> [TypeArg] -> Metadata -> CustomOp
makeOp opdef args = CustomOp (ext opdef) (opName opdef) (signature opdef args) args
