module Test.Arithmetic where

import Brat.Checker.Arithmetic

import Test.Tasty
import Test.Tasty.HUnit

test_simplify :: TestTree
test_simplify = testGroup "simplify" $
    [testCase "onevar" $
        let expected = (nsVar "x", nsConst 3)
            lhs = (nsConst 42) <> (nsVar "x" `nsMul` 10)
            rhs = (nsConst 63) <> (nsVar "x" `nsMul` 3)
        in expected @=? simplify (lhs, rhs)
    ,testCase "multi" $
      (nsVar "x", nsConst 1) @=? simplify (nsVar "x" `nsMul` 2 <> nsVar "y", nsVar "y" <> nsConst 2)
    ]
