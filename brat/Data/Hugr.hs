{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}

module Data.Hugr where

-- Definitions of data structures which make up a hugr.
-- There's a lot of mutual dependency, so this contains Ops, Types and Values.

import qualified  Data.Set as S

import Brat.Syntax.Simple

orderEdgeOffset :: Int
orderEdgeOffset = -1

data PortId node = Port
  { nodeId :: node
  , offset :: Int
  }
 deriving (Eq, Functor, Show)

-- We should be able to work out exact extension requirements for our functions,
-- but instead we'll overapproximate.
bratExts :: [ExtensionId]
bratExts =
 ["prelude"
 ,"arithmetic.int_ops"
 ,"arithmetic.int_types"
 ,"arithmetic.float_ops"
 ,"arithmetic.float_types"
 ,"collections"
 ,"logic"
 ,"tket2.quantum"
 ,"BRAT"
 ]


------------------------------------- TYPES ------------------------------------
-------------------------  (Depends on HugrValue and Hugr)  --------------------

data UnitSum = UnitSum { size :: Int }
 deriving (Eq, Show)
data GeneralSum = GeneralSum { row :: [[HugrType]] }
 deriving (Eq, Show)

data SumType = SU UnitSum | SG GeneralSum
 deriving (Eq, Show)

newtype SumOfRows = SoR [[HugrType]] deriving Show

type ExtensionId = String

-- Convert from a hugr sum of tuples to a SumOfRows
sumOfRows :: HugrType -> SumOfRows
sumOfRows (HTSum (SG (GeneralSum rows))) = SoR rows
sumOfRows ty = error $ show ty ++ " isn't a sum of row tuples"

compileSumOfRows :: SumOfRows -> HugrType
compileSumOfRows (SoR rows) = HTSum (SG (GeneralSum rows))

-- Depends on HugrValue (via TypeArg in HTOpaque)
data HugrType
  = HTQubit
  | HTUSize
  | HTArray
  | HTString
  | HTSum SumType
  | HTOpaque {-extension :: -}String {-type id :: -}String [TypeArg] TypeBound
  | HTFunc PolyFuncType
  | HTAny
 deriving (Eq, Show)

htTuple :: [HugrType] -> HugrType
htTuple row = HTSum (SG (GeneralSum [row]))

htRotation :: HugrType
htRotation = HTOpaque "tket.rotation" "rotation" [] TBCopy

data PolyFuncType = PolyFuncType
 { params :: [TypeParam]
 , body   :: FunctionType
 } deriving (Eq, Show)

data CustomTypeArg = CustomTypeArg
 { typ :: CustomType
 , value :: HugrValue
 } deriving (Eq, Show)

data CustomType deriving (Eq, Show)

data TypeBound = TBEq | TBCopy | TBAny deriving (Eq, Ord, Show)

data TypeArgVariable = TypeArgVariable
 { idx :: Int
 , cached_decl :: TypeParam
 }
 deriving (Eq, Show)

data TypeArg
 = TAType HugrType
 | TANat Int
 | TAOpaque CustomTypeArg
 | TASequence [TypeArg]
 | TAVariable TypeArgVariable
 deriving (Eq, Show)

data TypeParam = TypeParam deriving (Eq, Show)

data FunctionType = FunctionType
 { input :: [HugrType]
 , output :: [HugrType]
 , extensions :: [ExtensionId]
 } deriving (Eq, Show)

data Array = Array
 { ty :: HugrType
 , len :: Int
 } deriving Show

boundOf :: HugrType -> TypeBound
boundOf HTQubit = TBAny
boundOf (HTOpaque _ _ _ b) = b
boundOf HTUSize = TBEq
boundOf (HTSum (SU _)) = TBEq
boundOf (HTSum (SG (GeneralSum rows))) = maximum (TBEq:(boundOfList <$> rows))
 where
  boundOfList :: [HugrType] -> TypeBound
  boundOfList [] = TBEq
  boundOfList xs = maximum (boundOf <$> xs)
boundOf (HTFunc _) = TBCopy
boundOf _ = error "unimplemented bound"

hugrList :: HugrType -> HugrType
hugrList ty = HTOpaque "Collections" "List" [TAType ty] (boundOf ty)

intWidth :: Int
intWidth = 6  -- 2^6 = 64 bits

hugrInt :: HugrType
hugrInt = HTOpaque "arithmetic.int.types" "int" [TANat intWidth] TBEq

hugrFloat :: HugrType
hugrFloat = HTOpaque "arithmetic.float.types" "float64" [] TBCopy


------------------------------------ VALUES ------------------------------------
-----------------------  (Depends on Hugr and HugrType)  -----------------------

-- Depends on `Hugr` and on `HugrType` (for `HVExtension`)
data HugrValue
 = HVFunction (Hugr Int)
 | HVTuple [HugrValue]
 | HVExtension [ExtensionName] HugrType CustomConst
 | HVUSize Int
 | HVISize Int
 | HVString String
 | HVFloat Double
 deriving (Eq, Show)

hvUnit = HVTuple []
hvRotation rad = HVExtension
                 ["tket.rotation"]
                 htRotation
                 (CC "ConstRotation" [("half_turns", HVFloat (rad / pi))])

valFromSimple :: SimpleTerm -> HugrValue
valFromSimple (Num x) = HVISize x
valFromSimple (Float x) = HVFloat x
valFromSimple (Text t) = HVString t
valFromSimple Unit = hvUnit

-------------------------------------- OPS -------------------------------------
---------------------  (Depends on HugrValue and HugrType) ---------------------

data ModuleOp = ModuleOp deriving (Eq, Show)

data FuncDefn = FuncDefn
 { name :: String
 , signature_ :: PolyFuncType
 , metadata :: [(String, String)]
 } deriving (Eq, Show)

data CustomConst = CC String [(String, HugrValue)] -- Named type args
 deriving Eq

instance Show CustomConst where
  show (CC tag cts) = "Const(" ++ tag ++ ")(" ++ show cts ++ ")"

type ExtensionName = String

data ConstOp = ConstOp
 { const :: HugrValue
 } deriving (Eq, Show)

data InputNode = InputNode
 { types  :: [HugrType]
 , metadata :: [(String, String)]
 } deriving (Eq, Show)

data OutputNode = OutputNode
 { types  :: [HugrType]
 , metadata :: [(String, String)]
 } deriving (Eq, Show)

data Conditional = Conditional
 { sum_rows :: [[HugrType]]
 , other_inputs :: [HugrType]
 , outputs :: [HugrType]
 , metadata :: [(String, String)]
 } deriving (Eq, Show)

data Case = Case
  { signature_ :: FunctionType
  , metadata :: [(String, String)]
  } deriving (Eq, Show)

data DFG = DFG
 { signature_ :: FunctionType
 , metadata :: [(String, String)]
 } deriving (Eq, Show)

data TagOp = TagOp
 { tag :: Int
 , variants :: [[HugrType]]
 , metadata :: [(String, String)]
 } deriving (Eq, Show)

data MakeTupleOp = MakeTupleOp
 { tys :: [HugrType]
 } deriving (Eq, Show)

data CustomOp = CustomOp
  { extension :: String
  , op_name :: String
  , signature_ :: FunctionType
  , args :: [TypeArg]
  } deriving (Eq, Show)

-- In BRAT, we're not using the type parameter machinery of hugr for
-- polymorphism, so calls can just take simple signatures.
--
-- Type args are only given to our custom ops, and this is done at the time of
-- adding the op, rather than when it is called.
--
-- TODO: Instead of using hugr type args, we should be using coercions for
-- polymorphic function arguments.
data CallOp = CallOp
  { signature_ :: FunctionType
  } deriving (Eq, Show)

intOp :: String -> [HugrType] -> [HugrType] -> [TypeArg] -> CustomOp
intOp opName ins outs = CustomOp "arithmetic.int_ops" opName (FunctionType ins outs ["arithmetic.int_ops"])

binaryIntOp :: String -> CustomOp
binaryIntOp name
 = intOp name [hugrInt, hugrInt] [hugrInt] [TANat intWidth]

floatOp :: String -> [HugrType] -> [HugrType] -> [TypeArg] -> CustomOp
floatOp opName ins outs = CustomOp "arithmetic.float_ops" opName (FunctionType ins outs ["arithmetic.float_ops"])

binaryFloatOp :: String -> CustomOp
binaryFloatOp name = floatOp name [hugrFloat, hugrFloat] [hugrFloat] []

data CallIndirectOp = CallIndirectOp
  { signature_ :: FunctionType
  } deriving (Eq, Show)

holeOp :: Int -> FunctionType -> CustomOp
holeOp idx sig = CustomOp "BRAT" "Hole" sig
                        [TANat idx, TAType (HTFunc (PolyFuncType [] sig))]

isHole :: HugrOp -> Maybe (Int, FunctionType)
isHole (OpCustom (CustomOp "BRAT" "Hole" sig args)) =
  let [TANat idx, _] = args in Just (idx, sig) -- crash rather than return false for bad args
isHole _ = Nothing

-- TYPE ARGS:
--  * A length-2 sequence comprising:
--    * A sequence of types (the inputs of outerSig)
--    * A sequence of types (the outputs of outerSig)
--  * A sequence of such length-2 sequences of the input and output types for each innerSig
-- INPUTS:
--  * A graph (of type outerSig)
--  * Many graphs with types given by innerSigs (to go in the holes)
-- OUTPUT:
--  * A single graph whose signature is the same as outerSig
substOp :: {- outerSig :: -}FunctionType
        -> {- innerSigs :: -}[FunctionType]{- length n -}
        -> CustomOp
substOp outerSig innerSigs
  = CustomOp "BRAT" "Substitute" sig [toArg outerSig, TASequence (toArg <$> innerSigs)]
 where
  fnExts (FunctionType _ _ exts) = S.fromList exts
  combinedExts = S.toList $ foldr S.union (fnExts outerSig) (fnExts <$> innerSigs)

  sig = FunctionType (toFunc <$> (outerSig : innerSigs)) [toFunc outerSig] combinedExts
  toArg = TAType . HTFunc . PolyFuncType []

toFunc :: FunctionType -> HugrType
toFunc ty = HTFunc (PolyFuncType [] ty)

toSeq :: [HugrType] -> TypeArg
toSeq tys = TASequence (TAType <$> tys)

partialOp :: FunctionType  -- Signature of the function that is partially evaluated
          -> Int  -- Number of arguments that are evaluated
          -> CustomOp
partialOp funcSig numSupplied = CustomOp "BRAT" "Partial" sig args
 where
  sig :: FunctionType
  sig = FunctionType
        (toFunc funcSig : partialInputs)
        [toFunc (FunctionType otherInputs (output funcSig) (extensions funcSig))]
        ["BRAT"]
  args = [toSeq partialInputs, toSeq otherInputs, toSeq (output funcSig)]

  partialInputs = take numSupplied (input funcSig)
  otherInputs = drop numSupplied (input funcSig)


data LoadConstantOp = LoadConstantOp
  { datatype :: HugrType
  } deriving (Eq, Show)

data LoadFunctionOp = LoadFunctionOp
  { func_sig :: PolyFuncType
  , type_args :: [TypeArg]
  , signature :: FunctionType
  } deriving (Eq, Show)

data NoopOp = NoopOp
  { ty :: HugrType
  } deriving (Eq, Show)

-- In the order they must be printed in - roots, inputs, outputs
data HugrOp
  -- OpConditional should be compiled last so we can sort out its parent
  = OpMod ModuleOp
  | OpIn InputNode
  | OpOut OutputNode
  -- the rest
  | OpDefn FuncDefn
  | OpDFG DFG
  | OpConst ConstOp
  | OpConditional Conditional
  | OpCase Case
  | OpTag TagOp
  | OpMakeTuple MakeTupleOp
  | OpCustom CustomOp
  | OpCall CallOp
  | OpCallIndirect CallIndirectOp
  | OpLoadConstant LoadConstantOp
  | OpLoadFunction LoadFunctionOp
  | OpNoop NoopOp
 deriving (Eq, Show)

addMetadata :: [(String, String)] -> HugrOp -> HugrOp
addMetadata md (OpDFG (DFG { .. })) = OpDFG (DFG { metadata = metadata ++ md, .. })
addMetadata md (OpCase (Case { .. })) = OpCase (Case { metadata = metadata ++ md, .. })
addMetadata md (OpIn (InputNode { .. })) = OpIn (InputNode { metadata = metadata ++ md, .. })
addMetadata md (OpTag (TagOp { .. })) = OpTag (TagOp { metadata = metadata ++ md, .. })
addMetadata md (OpDefn (FuncDefn { .. })) = OpDefn (FuncDefn { metadata = metadata ++ md, .. })
addMetadata md (OpConditional (Conditional { .. })) = OpConditional (Conditional { metadata = metadata ++ md, .. })
addMetadata _ op = op

data Hugr node = Hugr ([(node, HugrOp)], [(PortId node, PortId node)]) deriving (Eq, Show)
