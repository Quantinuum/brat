module Test.Arithmetic where

import Brat.Checker.Arithmetic

import Test.Tasty
import Test.Tasty.HUnit

test_simplify :: TestTree
test_simplify = testGroup "simplify" $
    [testCase "gcd_and_flip" $
       (sVar "x" `sMul` 2, sVar "y" <> sConst 3) @=? simplify (sConst 6 <> (sVar "y" `sMul` 2), sVar "x" `sMul` 4)
    ,testCase "onevar" $
        let expected = (sVar "x", sConst 3)
            lhs = (sConst 42) <> (sVar "x" `sMul` 10)
            rhs = (sConst 63) <> (sVar "x" `sMul` 3)
        in expected @=? simplify (lhs, rhs)
    ,testCase "multi" $
      (sVar "x", sConst 1) @=? simplify (sVar "x" `sMul` 2 <> sVar "y", sVar "y" <> sConst 2)
    ]