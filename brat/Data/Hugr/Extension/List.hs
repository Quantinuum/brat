module Data.Hugr.Extension.List where

import Data.Hugr (htEither, htList, htOption
                 ,CustomOp(..), FunctionType(..), HugrType(..), TypeArg(..))
import Data.Hugr.Extension (OpDef(..), makeOp)

data ListOp
 = New
 | Discard
 | Pop
 | Push
 | Get
 | Set
 | Insert
 | Length
 deriving (Eq, Show)

instance OpDef ListOp where
  signature opdef [TAType elemTy] = case opdef of
    New     -> FunctionType [] [listTy] [ext opdef]
    Discard -> FunctionType [listTy] [] [ext opdef]
    Pop     -> FunctionType [listTy] [listTy, htOption [elemTy]] [ext opdef]
    Push    -> FunctionType [listTy, elemTy] [listTy] [ext opdef]
    Get     -> FunctionType [listTy, HTUSize]
                            [listTy, htOption [elemTy]]
                            [ext opdef]
    Set     -> FunctionType [listTy, HTUSize, elemTy]
                            [listTy, htEither [elemTy] [elemTy]]
                            [ext opdef]

    Insert  -> FunctionType [listTy ,HTUSize, elemTy]
                            [listTy, htEither [elemTy] []]
                            [ext opdef]
    Length  -> FunctionType [listTy] [listTy, HTUSize] [ext opdef]
   where listTy = htList elemTy
  signature _ _ = error "bad args"

  opName = \case
    New     -> "new"
    Discard -> "discard_empty"
    Pop     -> "pop"
    Push    -> "push"
    Get     -> "get"
    Set     -> "set"
    Insert  -> "insert"
    Length  -> "length"
  ext _ = "collections.list"

listOp :: ListOp -> HugrType -> CustomOp
listOp opdef ht = makeOp opdef [TAType ht]
