module Brat.LSP.Holes where

import Brat.Checker.Types (TypedHole(..), HoleData(..))
import Brat.FC (FC)
import Brat.Syntax.Common (UserNameMap)
import Brat.Syntax.Value (ShowWithMetas(..))

holeInfo :: UserNameMap -> TypedHole -> (FC, String)
holeInfo m h@(TypedHole _ HoleData { .. }) = (fc,
                                              unlines (showWithMetas m h : maybe [] (delim:) suggestions)
                                             )
 where
  delim = replicate (length (showWithMetas m h)) '-'
