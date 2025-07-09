module Brat.Constructors.Patterns where

import Brat.QualName

pattern CSucc, CDoub, CNil, CCons, CSome, CNone, CTrue, CFalse, CZero, CSnoc,
        CConcatEqEven, CConcatEqOdd, CRiffle, CRefl :: QualName
pattern CSucc = PrefixName [] "succ"
pattern CDoub = PrefixName [] "doub"
pattern CNil = PrefixName [] "nil"
pattern CSome = PrefixName [] "some"
pattern CNone = PrefixName [] "none"
pattern CTrue = PrefixName [] "true"
pattern CFalse = PrefixName [] "false"
pattern CZero = PrefixName [] "zero"
pattern CCons = PrefixName [] "cons"
pattern CSnoc = PrefixName [] "snoc"
pattern CConcatEqEven = PrefixName [] "concatEqEven"
pattern CConcatEqOdd = PrefixName [] "concatEqOdd"
pattern CRiffle = PrefixName [] "riffle"
pattern CRefl = PrefixName [] "refl"
pattern COmit = PrefixName [] "omit"

pattern CList, CVec, CNat, CInt, COption, CBool, CBit, CFloat, CString, CEq :: QualName
pattern CList = PrefixName [] "List"
pattern CVec = PrefixName [] "Vec"
pattern CNat = PrefixName [] "Nat"
pattern CInt = PrefixName [] "Int"
pattern COption = PrefixName [] "Option"
pattern CBool = PrefixName [] "Bool"
pattern CBit = PrefixName [] "Bit"
pattern CFloat = PrefixName [] "Float"
pattern CString = PrefixName [] "String"
pattern CEq = PrefixName [] "Eq"
pattern CThin = PrefixName [] "Thin"

pattern CQubit, CMoney :: QualName
pattern CQubit = PrefixName [] "Qubit"
pattern CMoney = PrefixName [] "Money"
