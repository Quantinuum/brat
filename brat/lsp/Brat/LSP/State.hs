module Brat.LSP.State (ProgramState(..), emptyPS, updateState) where

import Brat.Checker.Types (TypedHole)
import Brat.Load (VDecl)
import Brat.Syntax.Raw

data ProgramState
  = PS { decls :: [VDecl]
       , aliases :: [(String, TypeAlias)]
       , holes :: [TypedHole]
       }
    deriving Show

emptyPS :: ProgramState
emptyPS = PS [] [] []

updateState :: ([VDecl], [TypedHole]) -> ProgramState -> ProgramState
updateState (decls, holes) st = st { decls = decls, holes = holes }
