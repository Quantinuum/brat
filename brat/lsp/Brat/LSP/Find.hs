{-# LANGUAGE DataKinds, GADTs #-}

module Brat.LSP.Find (Context(..), getInfo) where

import Data.List.NonEmpty (NonEmpty(..), toList)
import Data.Maybe (mapMaybe)

import Brat.FC
import Brat.Load (VDecl(..))
import Brat.LSP.State
import Brat.Syntax.Common
import Brat.Syntax.Concrete (Flat(..))
import Brat.Syntax.Core
import Brat.Syntax.FuncDecl (FunBody(..), FuncDecl(..))
import Brat.Unelaborator (unelab)

data Context
  = Context { declName :: String
            , root :: Flat
            -- May be nothing if not hovering over a term
            , thing :: Flat
            } deriving Show

getInfo :: ProgramState -> Pos -> Maybe Context
getInfo ps pos
  = case filter pred (decls ps) of
      [] -> Nothing
      (x:_) -> buildContext pos x
 where
  pred :: VDecl -> Bool
  pred (VDecl (FuncDecl{..})) = pos `inside` fnLoc

  buildContext :: Pos -> VDecl -> Maybe Context
  buildContext pos (VDecl FuncDecl{..}) = do
    body <- findInBody pos fnBody
    subject <- getThing pos body
    pure $ Context { declName = fnName
                   , root = unWC body
                   , thing = subject
                   }

  findInBody :: KINDY k => Pos -> FunBody Term k -> Maybe (WC Flat)
  findInBody pos (NoLhs (WC fc rhs))
    | pos `inside` fc = Just (WC fc (unelab Chky kindy rhs))
  -- TODO: Doesn't search in LHS
  findInBody pos (Clauses (c :| cs)) = findInClauses (c:cs)
   where
    findInClauses :: [(WC Abstractor, WC (Term Chk Noun))] -> Maybe (WC Flat)
    findInClauses [] = Nothing
    findInClauses ((_, rhs):cs)
     | rfc <- fcOf rhs, pos `inside` rfc = Just (unelab Chky Nouny <$> rhs)
     | otherwise = findInClauses cs
  findInBody _ _ = Nothing

  getThing :: Pos -> WC Flat -> Maybe Flat
  getThing pos (WC fc x)
    | pos `inside` fc = case mapMaybe (getThing pos) (subTerms x) of
                          [] -> Just x
                          -- xs should be the empty list, but I don't think it's
                          -- worth crashing the server over
                          (x:_) -> Just x
    | otherwise = Nothing

-- Helper function for getting the nested terms from a Flat term, so that we can
-- dig through them to find the most local thing which matches the FC.
subTerms :: Flat -> [WC Flat]
subTerms (FApp a b) = [a, b]
subTerms (FJuxt a b) = [a, b]
subTerms (FThunk th) = [th]
subTerms (FCompose a b) = [a,  b]
subTerms (FInto a b) = [a, b]
subTerms (FLambda lclauses) = snd <$> toList lclauses
subTerms (FAnnotation tm _) = [tm]
subTerms (FLetIn _ a b) = [a, b]
subTerms (FCon _ arg) = [arg]
subTerms (FPull _ tm) = [tm]
subTerms _ = []
