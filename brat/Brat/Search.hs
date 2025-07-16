module Brat.Search (vsearch) where

import Brat.Constructors (CtorArgs(..), defaultConstructors)
import Brat.FC
import Brat.QualName
import Brat.Syntax.Core
import Brat.Syntax.Common
import Brat.Syntax.Value
import Brat.Syntax.Simple
import Hasochism

import Control.Monad (guard)
import Data.Either (isRight)
import qualified Data.Map as M
import Data.Type.Equality ((:~:)(..))

vec :: FC -> [WC (Term Chk Noun)] -> Term Chk Noun
vec fc [] = Con (plain "nil") (WC fc Empty)
vec fc (x:xs) = Con (plain "cons") (WC fc (x :|: WC fc (vec fc xs)))

binders :: Int -> Abstractor
binders n = foldr1 (:||:) $ take n (APat . Bind . (:[]) <$> ['a'..])

-- TODO: Extend this to Ro's with binders
tokenRow :: FC -> (Val Z -> [Term Chk Noun]) -> Ro m Z Z -> [Term Chk Noun]
tokenRow fc f r = foldr1 comma <$> tokenRows r
 where
  comma a b = WC fc a :|: WC fc b

  tokenRows R0 = [[]]
  tokenRows (RPr (_, x) xs) = do
    tm <- f x
    rest <- tokenRows xs
    [tm:rest]
  -- No suggestions for kinds. If we had some, should combine with tokenRows of the rest as above.
  tokenRows (REx _ _) = []

-- Easiest answers
-- TODO: Expand this to include open types
-- at the moment, this only works for very simple types (no dependency anywhere near)
tokenValues :: FC -> Val Z -> [Term Chk Noun]
tokenValues _ TNat = Simple . Num <$> [0..]
tokenValues _ TInt = Simple . Num <$> [0..]
tokenValues _ TFloat = Simple . Float <$> [0.0..]
tokenValues _ TText = Simple . Text <$> ("":((:[])<$>['A'..]))
tokenValues fc (TOption ty) = (:) (Con (plain "none") (WC fc Empty)) $ do
  val <- tokenValues fc ty
  [Con (plain "some") (WC fc val)]
tokenValues fc (TList ty) = concat $ do
  tm <- tokenValues fc ty
  list <- iterate (tm:) []
  [[vec fc (WC fc <$> list)]]
tokenValues fc (TVec ty (VNum (NumValue n Constant0))) = do
  tm <- tokenValues fc ty
  [vec fc (replicate (fromIntegral n) $ WC fc tm)]
tokenValues _ (TVec _ _) = [] -- not enough info
-- HACK: Lookup in the default constructor table, rather than using the Checking
-- monad to look up definitions.
-- TODO: Have a failure mode. We should also
tokenValues fc (VCon tyCon tyArgs) = do
  (ctor, tbl) <- M.toList defaultConstructors
  -- TODO: Match `tyArgs` against `pats` and use the resulting values to
  -- instantiate
  (tblTyCon, CArgs pats _ _tyArgRo consArgRo) <- M.toList tbl
  guard (tyCon == tblTyCon)
  -- TODO: The values coming back from this should be used to contextualise the
  -- types in `consArgRo`.
  guard (isRight (valMatches tyArgs pats))
  -- HACK: to deal only with constructors that take no arguments
  case consArgRo of
    R0 -> [Con ctor (WC fc Empty)]
    _ -> []
tokenValues fc (VFun Braty (ss :->> ts)) =
  [ Th (WC fc (Lambda (WC fc abs, WC fc t) [])) | t <- rhs ]
 where
  abs = binders (rowLen ss)

  rhs = outputsClosed (ss, ts) >>= outputsNonBinding >>= tokenRow fc (tokenValues fc)

  -- Throw away inputs, but if they don't bind anything return closed output row
  outputsClosed :: (Ro Brat Z i, Ro Brat i j) -> [Ro Brat Z j]
  outputsClosed (R0, outs) = [outs]
  outputsClosed (RPr _ ro, outs) = outputsClosed (ro, outs)
  outputsClosed (REx _ _, _) = []

  outputsNonBinding :: Ro Brat Z j -> [Ro Brat Z Z]
  outputsNonBinding R0 = [R0]
  outputsNonBinding (RPr stuff ro) = RPr stuff <$> outputsNonBinding ro
  outputsNonBinding (REx _ _) = []


tokenValues fc (VFun Kerny (ss :->> ts)) =
  [ Th (WC fc (Lambda (WC fc abs, WC fc t) [])) | t <- rhs ]
 where
  abs = binders (rowLen ss)
  rhs = case (kernelNoBind ss, kernelNoBind ts) of
    (Refl, Refl) -> tokenRow fc tokenSType ts

  tokenSType :: Val Z -> [Term Chk Noun]
  tokenSType TQ = []
  tokenSType TBit = tokenValues fc TBool
  tokenSType (TVec TQ _) = []
  tokenSType (TVec sty (VNum (NumValue n Constant0))) = do
    tm <- tokenSType sty
    [vec fc (replicate (fromIntegral n) $ WC fc tm)]
  tokenSType _ = []
tokenValues _ _ = []

rowLen :: Ro m bot top -> Int
rowLen R0 = 0
rowLen (REx _ rest) = 1 + rowLen rest
rowLen (RPr _ rest) = 1 + rowLen rest

vsearch :: FC -> Val Z -> [Term Chk Noun]
vsearch fc = take 5 . tokenValues fc
