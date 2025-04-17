module Brat.LSP.State (ProgramState(..), emptyPS, updateState) where

import Brat.Checker.Types (TypedHole)
import Brat.Syntax.Raw
import Brat.Syntax.Value (ShowWithMetas(..), VDecl)

data ProgramState
  = PS { decls :: [VDecl]
       , aliases :: [(String, TypeAlias)]
       , holes :: [TypedHole]
       }

instance ShowWithMetas ProgramState where
  showWithMetas m (PS {..}) = unlines ("Decls:":(showWithMetas m <$> decls) ++
                                       ("":"Aliases:":(show <$> aliases)) ++
                                       ("":"Holes:":(showWithMetas m <$> holes))
                                      )

emptyPS :: ProgramState
emptyPS = PS [] [] []

updateState :: ([VDecl], [TypedHole]) -> ProgramState -> ProgramState
updateState (decls, holes) st = st { decls = decls, holes = holes }
