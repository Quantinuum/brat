{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}

module Data.Hugr where

-- Definitions of data structures which make up a hugr, along with serialisation
-- to JSON. There's a lot of mutual dependency, so this contains Ops, Types and
-- Values.

import Data.Aeson
import qualified Data.Aeson.KeyMap as KeyMap
import qualified  Data.Set as S
import Data.Text (Text, pack)

import Brat.Syntax.Simple

orderEdgeOffset :: Int
orderEdgeOffset = -1

data PortId node = Port
  { nodeId :: node
  , offset :: Int
  }
 deriving (Eq, Functor, Show)

instance ToJSON node => ToJSON (PortId node) where
  toJSON (Port node offset) = toJSON (node, offset')
    where offset' = if offset == orderEdgeOffset then Nothing else Just offset

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
  | HTSum SumType
  | HTOpaque {-extension :: -}String {-type id :: -}String [TypeArg] TypeBound
  | HTFunc PolyFuncType
 deriving (Eq, Show)

class JSONParent n where
  toJSONp :: n -> Value -> Value

instance ToJSON HugrType where
  toJSON HTQubit = object ["t" .= ("Q" :: Text)]
  toJSON (HTSum (SU (UnitSum size))) = object ["t" .= ("Sum" :: Text)
                                              ,"s" .= ("Unit" :: Text)
                                              ,"size" .= size
                                              ]
  toJSON (HTSum (SG (GeneralSum rows))) = object ["t" .= ("Sum" :: Text)
                                                 ,"s" .= ("General" :: Text)
                                                 ,"rows" .= rows
                                                 ]
  toJSON HTUSize = object ["t" .= ("I" :: Text)]
  toJSON (HTOpaque ext id args bound) = object ["t" .= ("Opaque" :: Text)
                                               ,"extension" .= pack ext
                                               ,"id" .= pack id
                                               ,"args" .= args
                                               ,"bound" .= bound
                                               ]
  toJSON (HTFunc sig) = object ["t" .= ("G" :: Text)
                               ,"input" .= input (body sig)
                               ,"output" .= output (body sig)
                               ,"extension_reqs" .= extensions (body sig)
                               ]
  toJSON ty = error $ "todo: json of " ++ show ty

htTuple :: [HugrType] -> HugrType
htTuple row = HTSum (SG (GeneralSum [row]))

data PolyFuncType = PolyFuncType
 { params :: [TypeParam]
 , body   :: FunctionType
 } deriving (Eq, Show)

instance ToJSON PolyFuncType where
  toJSON (PolyFuncType params body) = object ["t" .= ("G" :: Text)
                                             ,"params" .= params
                                             ,"body" .= body
                                             ]

data CustomTypeArg = CustomTypeArg
 { typ :: CustomType
 , value :: HugrValue
 } deriving (Eq, Show)

data CustomType deriving (Eq, Show)

data TypeBound = TBEq | TBCopy | TBAny deriving (Eq, Ord, Show)

instance ToJSON TypeBound where
  toJSON TBEq = "E"
  toJSON TBCopy = "C"
  toJSON TBAny = "A"

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

instance ToJSON TypeArg where
  toJSON (TAType ty) = object ["tya" .= ("Type" :: Text)
                              ,"ty" .= ty
                              ]
  toJSON (TANat n) = object ["tya" .= ("BoundedNat" :: Text)
                            ,"n" .= n
                            ]
  toJSON (TASequence args) = object ["tya" .= ("Sequence" :: Text)
                                    ,"elems" .= args
                                    ]

data TypeParam = TypeParam deriving (Eq, Show)
instance ToJSON TypeParam where
  toJSON = undefined

data FunctionType = FunctionType
 { input :: [HugrType]
 , output :: [HugrType]
 , extensions :: [ExtensionId]
 } deriving (Eq, Show)

instance ToJSON FunctionType where
  toJSON (FunctionType ins outs exts) = object ["input" .= ins
                                               ,"output" .= outs
                                               ,"extension_reqs" .= exts
                                               ]

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
 deriving (Eq, Show)

instance ToJSON HugrValue where
  toJSON (HVFunction h) = object ["v" .= ("Function" :: Text)
                                 ,"hugr" .= h
                                 ]
  toJSON (HVTuple vs) = object ["v" .= ("Tuple" :: Text)
                                  ,"vs" .= vs
                                  ]
  toJSON (HVExtension exts ty val) = object ["v" .= ("Extension" :: Text)
                                            ,"typ" .= ty
                                            ,"value" .= val
                                            ,"extensions" .= exts
                                            ]

hvUnit = HVTuple []
hvFloat x = HVExtension ["arithmetic.float_types"] hugrFloat
            (CC "ConstF64" (KeyMap.singleton "value" x))
hvInt x = HVExtension ["arithmetic.int_types"] hugrInt
          (CC "ConstInt" (KeyMap.insert "log_width" 6 (KeyMap.singleton "value" x)))

valFromSimple :: SimpleTerm -> HugrValue
valFromSimple (Num x) = hvInt x
valFromSimple (Float x) = hvFloat x
valFromSimple (Text _) = error "todo"
valFromSimple Unit = hvUnit

-------------------------------------- OPS -------------------------------------
---------------------  (Depends on HugrValue and HugrType) ---------------------

data ModuleOp = ModuleOp deriving (Eq, Show)

instance JSONParent ModuleOp where
  toJSONp ModuleOp parent = object ["parent" .= parent
                                   ,"op" .= ("Module" :: Text)
                                   ]

data FuncDefn = FuncDefn
 { name :: String
 , signature_ :: PolyFuncType
 , metadata :: [(String, String)]
 } deriving (Eq, Show)

instance JSONParent FuncDefn where
  toJSONp (FuncDefn { .. }) parent = object ["parent" .= parent
                                            ,"op" .= ("FuncDefn" :: Text)
                                            ,"name" .= name
                                            ,"signature" .= signature_
                                            ,"metadata" .= metadata
                                            ]

data CustomConst where
  CC :: forall a. (Eq a, Show a, ToJSON a) => String -> a -> CustomConst

instance Eq CustomConst where
  (CC tag cts) == (CC tag' cts') = tag == tag' && (toJSON cts == toJSON cts')

instance Show CustomConst where
  show (CC tag cts) = "Const(" ++ tag ++ ")(" ++ show cts ++ ")"

instance ToJSON CustomConst where
  toJSON (CC tag cts) = object ["c" .= pack tag
                               ,"v" .= cts
                               ]

type ExtensionName = String

data ConstOp = ConstOp
 { const :: HugrValue
 } deriving (Eq, Show)

instance JSONParent ConstOp where
  toJSONp (ConstOp {..}) parent = object ["parent" .= parent
                                         ,"op" .= ("Const" :: Text)
                                         ,"v" .= const
                                         ]



data InputNode = InputNode
 { types  :: [HugrType]
 , metadata :: [(String, String)]
 } deriving (Eq, Show)

instance JSONParent InputNode where
  toJSONp (InputNode types metadata) parent = object ["parent" .= parent
                                                     ,"op" .= ("Input" :: Text)
                                                     ,"types" .= types
                                                     ,"metadata" .= metadata
                                                     ]

data OutputNode = OutputNode
 { types  :: [HugrType]
 , metadata :: [(String, String)]
 } deriving (Eq, Show)

instance JSONParent OutputNode where
  toJSONp (OutputNode { .. }) parent = object ["parent" .= parent
                                              ,"op" .= ("Output" :: Text)
                                              ,"types" .= types
                                              ,"metadata" .= metadata
                                              ]

data Conditional = Conditional
 { sum_rows :: [[HugrType]]
 , other_inputs :: [HugrType]
 , outputs :: [HugrType]
 , metadata :: [(String, String)]
 } deriving (Eq, Show)

instance JSONParent Conditional where
  toJSONp (Conditional { .. }) parent
   = object ["op" .= ("Conditional" :: Text)
            ,"parent" .= parent
            ,"sum_rows" .= sum_rows
            ,"other_inputs" .= other_inputs
            ,"outputs" .= outputs
            ,"extension_delta" .= ([] :: [Text])
            ,"metadata" .= metadata
            ]

data Case = Case
  { signature_ :: FunctionType
  , metadata :: [(String, String)]
  } deriving (Eq, Show)

instance JSONParent Case where
  toJSONp (Case { .. }) parent = object ["op" .= ("Case" :: Text)
                                        ,"parent" .= parent
                                        ,"signature" .= signature_
                                        ,"metadata" .= metadata
                                        ]

{-
data Const = Const
 { parent :: Int
 , value :: HugrValue
 , typ :: HugrType
 }
-}

data DFG = DFG
 { signature_ :: FunctionType
 , metadata :: [(String, String)]
 } deriving (Eq, Show)

instance JSONParent DFG where
  toJSONp (DFG { .. }) parent = object ["op" .= ("DFG" :: Text)
                                       ,"parent" .= parent
                                       ,"signature" .= signature_
                                       ,"metadata" .= metadata
                                       ]

data TagOp = TagOp
 { tag :: Int
 , variants :: [[HugrType]]
 , metadata :: [(String, String)]
 } deriving (Eq, Show)

instance JSONParent TagOp where
  toJSONp (TagOp tag variants metadata) parent
   = object ["parent" .= parent
            ,"op" .= ("Tag" :: Text)
            ,"tag" .= tag
            ,"variants" .= variants
            ,"metadata" .= metadata
            ]

data MakeTupleOp = MakeTupleOp
 { tys :: [HugrType]
 } deriving (Eq, Show)

instance JSONParent MakeTupleOp where
  toJSONp (MakeTupleOp tys) parent
   = object ["parent" .= parent
            ,"op" .= ("MakeTuple" :: Text)
            ,"tys" .= tys
            ]

data CustomOp = CustomOp
  { extension :: String
  , op_name :: String
  , signature_ :: FunctionType
  , args :: [TypeArg]
  } deriving (Eq, Show)

instance JSONParent CustomOp where
  toJSONp (CustomOp { .. }) parent = object ["parent" .= parent
                                            ,"op" .= ("CustomOp" :: Text)
                                            ,"description" .= ("" :: Text)
                                            ,"extension" .= pack extension
                                            ,"args" .= args
                                            ,"op_name" .= pack op_name
                                            ,"signature" .= signature_
                                            ]

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

instance JSONParent CallOp where
  toJSONp (CallOp signature_) parent =
    object ["parent" .= parent
           ,"op" .= ("Call" :: Text)
           ,"func_sig" .= PolyFuncType [] signature_
           ,"type_args" .= ([] :: [TypeArg])
           ,"instantiation" .= signature_
           ]

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

instance JSONParent CallIndirectOp where
  toJSONp (CallIndirectOp signature_) parent = object ["parent" .= parent
                                                      ,"signature" .= signature_
                                                      ,"op" .= ("CallIndirect" :: Text)
                                                      ]

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

instance JSONParent LoadConstantOp where
  toJSONp (LoadConstantOp {..}) parent = object ["parent" .= parent
                                                ,"op" .= ("LoadConstant" :: Text)
                                                ,"datatype" .= datatype
                                                ]

data LoadFunctionOp = LoadFunctionOp
  { func_sig :: PolyFuncType
  , type_args :: [TypeArg]
  , signature :: FunctionType
  } deriving (Eq, Show)

instance JSONParent LoadFunctionOp where
  toJSONp (LoadFunctionOp {..}) parent = object ["parent" .= parent
                                                ,"op" .= ("LoadFunction" :: Text)
                                                ,"func_sig" .= func_sig
                                                ,"type_args" .= type_args
                                                ,"signature" .= signature
                                                ]

data NoopOp = NoopOp
  { ty :: HugrType
  } deriving (Eq, Show)

instance JSONParent NoopOp where
  toJSONp (NoopOp {..}) parent = object ["parent" .= parent
                                        ,"op" .= ("Noop" :: Text)
                                        ,"ty" .= ty
                                        ]

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

instance JSONParent HugrOp where
  toJSONp (OpMod op) parent = toJSONp op parent
  toJSONp (OpDefn op) parent = toJSONp op parent
  toJSONp (OpConst op) parent = toJSONp op parent
  toJSONp (OpDFG op) parent = toJSONp op parent
  toJSONp (OpIn op) parent = toJSONp op parent
  toJSONp (OpOut op) parent = toJSONp op parent
  toJSONp (OpCase op) parent = toJSONp op parent
  toJSONp (OpConditional op) parent = toJSONp op parent
  toJSONp (OpTag op) parent = toJSONp op parent
  toJSONp (OpMakeTuple op) parent = toJSONp op parent
  toJSONp (OpCustom op) parent = toJSONp op parent
  toJSONp (OpCall op) parent = toJSONp op parent
  toJSONp (OpCallIndirect op) parent = toJSONp op parent
  toJSONp (OpLoadConstant op) parent = toJSONp op parent
  toJSONp (OpLoadFunction op) parent = toJSONp op parent
  toJSONp (OpNoop op) parent = toJSONp op parent

data Hugr node = Hugr ([(node, HugrOp)], [(PortId node, PortId node)]) deriving (Eq, Show)

instance ToJSON (Hugr Int) where
  toJSON (Hugr (nodes, edges)) = object
    ["version" .= ("v1" :: Text)
    ,"nodes" .= [toJSONp op (toJSON parent) | (parent, op) <- nodes]
    ,"edges" .= edges
    ,"encoder" .= ("BRAT" :: Text)
    ]
