{-# LANGUAGE OverloadedStrings #-}

module Test.Syntax.Let where

import Brat.Error (showError)
import Brat.Checker
import Brat.FC
import Brat.QualName
import Brat.Syntax.Common
import Brat.Syntax.Core
import Brat.Syntax.Simple
import Brat.Syntax.Value
import Test.Util (runEmpty)

import Data.String
import Test.Tasty.HUnit

instance IsString QualName where
  fromString = PrefixName []

instance IsString Abstractor where
  fromString = APat . Bind

fc = FC (Pos 0 0) (Pos 0 0)

test = testCase "let" $
  let num = dummyFC . Simple . Num
      tm = Let
        (dummyFC ("x" :||: "y"))
        (dummyFC (dummyFC (num 1 :|: num 2)
               ::: [("a", Right (Con (plain "Int") (dummyFC Empty)))
                   ,("b", Right (Con (plain "Int") (dummyFC Empty)))
                   ])
        )
        (dummyFC (Var "x"))
      conn = ((), ())
  in case fst <$> runEmpty (let ?my = Braty in let ?props = () in check (dummyFC tm) conn) of
       Right (((), [(_, Right TInt)]), ((), ())) -> pure ()
       Right (((), outs), ((), ())) -> assertFailure (show outs)
       Left err -> assertFailure (showError err)

letTests = test
