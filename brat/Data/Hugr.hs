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

data ModuleOp node = ModuleOp { parent :: node } deriving (Eq, Functor, Show)

instance Eq a => Ord (ModuleOp a) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (ModuleOp node) where
  toJSON (ModuleOp parent) = object ["parent" .= parent
                                    ,"op" .= ("Module" :: Text)
                                    ]

data FuncDefn node = FuncDefn
 { parent :: node
 , name :: String
 , signature_ :: PolyFuncType
 , metadata :: [(String, String)]
 } deriving (Eq, Functor, Show)

instance Eq a => Ord (FuncDefn a) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (FuncDefn node) where
  toJSON (FuncDefn { .. }) = object ["parent" .= parent
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

data ConstOp node = ConstOp
 { parent :: node
 , const :: HugrValue
 } deriving (Eq, Functor, Show)

instance Eq a => Ord (ConstOp a) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (ConstOp node) where
  toJSON (ConstOp {..}) = object ["parent" .= parent
                                 ,"op" .= ("Const" :: Text)
                                 ,"v" .= const
                                 ]



data InputNode node = InputNode
 { parent :: node
 , types  :: [HugrType]
 , metadata :: [(String, String)]
 } deriving (Eq, Functor, Show)

instance Eq a => Ord (InputNode a) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (InputNode node) where
  toJSON (InputNode parent types metadata) = object ["parent" .= parent
                                                    ,"op" .= ("Input" :: Text)
                                                    ,"types" .= types
                                                    ,"metadata" .= metadata
                                                    ]

data OutputNode node = OutputNode
 { parent :: node
 , types  :: [HugrType]
 , metadata :: [(String, String)]
 } deriving (Eq, Functor, Show)

instance Eq a => Ord (OutputNode a) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (OutputNode node) where
  toJSON (OutputNode { .. }) = object ["parent" .= parent
                                      ,"op" .= ("Output" :: Text)
                                      ,"types" .= types
                                      ,"metadata" .= metadata
                                      ]

data Conditional node = Conditional
 { parent :: node
 , sum_rows :: [[HugrType]]
 , other_inputs :: [HugrType]
 , outputs :: [HugrType]
 , metadata :: [(String, String)]
 } deriving (Eq, Functor, Show)

instance Eq a => Ord (Conditional a) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (Conditional node) where
  toJSON (Conditional { .. })
   = object ["op" .= ("Conditional" :: Text)
            ,"parent" .= parent
            ,"sum_rows" .= sum_rows
            ,"other_inputs" .= other_inputs
            ,"outputs" .= outputs
            ,"extension_delta" .= ([] :: [Text])
            ,"metadata" .= metadata
            ]

data Case node = Case
  { parent :: node
  , signature_ :: FunctionType
  , metadata :: [(String, String)]
  } deriving (Eq, Functor, Show)

instance Eq node => Ord (Case node) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (Case node) where
  toJSON (Case { .. }) = object ["op" .= ("Case" :: Text)
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

data DFG node = DFG
 { parent :: node
 , signature_ :: FunctionType
 , metadata :: [(String, String)]
 } deriving (Eq, Functor, Show)

instance Eq node => Ord (DFG node) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (DFG node) where
  toJSON (DFG { .. }) = object ["op" .= ("DFG" :: Text)
                               ,"parent" .= parent
                               ,"signature" .= signature_
                               ,"metadata" .= metadata
                               ]

data TagOp node = TagOp
 { parent :: node
 , tag :: Int
 , variants :: [[HugrType]]
 , metadata :: [(String, String)]
 } deriving (Eq, Functor, Show)

instance Eq node => Ord (TagOp node) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (TagOp node) where
  toJSON (TagOp parent tag variants metadata)
   = object ["parent" .= parent
            ,"op" .= ("Tag" :: Text)
            ,"tag" .= tag
            ,"variants" .= variants
            ,"metadata" .= metadata
            ]

data MakeTupleOp node = MakeTupleOp
 { parent :: node
 , tys :: [HugrType]
 } deriving (Eq, Functor, Show)

instance Eq node => Ord (MakeTupleOp node) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (MakeTupleOp node) where
  toJSON (MakeTupleOp parent tys)
   = object ["parent" .= parent
            ,"op" .= ("MakeTuple" :: Text)
            ,"tys" .= tys
            ]

data CustomOp node = CustomOp
  { parent :: node
  , extension :: String
  , op_name :: String
  , signature_ :: FunctionType
  , args :: [TypeArg]
  } deriving (Eq, Functor, Show)

instance Eq node => Ord (CustomOp node) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (CustomOp node) where
  toJSON (CustomOp { .. }) = object ["parent" .= parent
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
data CallOp node = CallOp
  { parent :: node
  , signature_ :: FunctionType
  } deriving (Eq, Functor, Show)

instance Eq node => Ord (CallOp node) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (CallOp node) where
  toJSON (CallOp parent signature_) =
    object ["parent" .= parent
           ,"op" .= ("Call" :: Text)
           ,"func_sig" .= PolyFuncType [] signature_
           ,"type_args" .= ([] :: [TypeArg])
           ,"instantiation" .= signature_
           ]

intOp :: node -> String -> [HugrType] -> [HugrType] -> [TypeArg] -> CustomOp node
intOp parent opName ins outs = CustomOp parent "arithmetic.int_ops" opName (FunctionType ins outs ["arithmetic.int_ops"])

binaryIntOp :: node -> String -> CustomOp node
binaryIntOp parent name
 = intOp parent name [hugrInt, hugrInt] [hugrInt] [TANat intWidth]

floatOp :: node -> String -> [HugrType] -> [HugrType] -> [TypeArg] -> CustomOp node
floatOp parent opName ins outs = CustomOp parent "arithmetic.float_ops" opName (FunctionType ins outs ["arithmetic.float_ops"])

binaryFloatOp :: node -> String -> CustomOp node
binaryFloatOp parent name = floatOp parent name [hugrFloat, hugrFloat] [hugrFloat] []

data CallIndirectOp node = CallIndirectOp
  { parent :: node
  , signature_ :: FunctionType
  } deriving (Eq, Functor, Show)

instance Eq node => Ord (CallIndirectOp node) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (CallIndirectOp node) where
  toJSON (CallIndirectOp parent signature_) = object ["parent" .= parent
                                                     ,"signature" .= signature_
                                                     ,"op" .= ("CallIndirect" :: Text)
                                                     ]

holeOp :: node -> Int -> FunctionType -> CustomOp node
holeOp parent idx sig = CustomOp parent "BRAT" "Hole" sig
                        [TANat idx, TAType (HTFunc (PolyFuncType [] sig))]

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
substOp :: node
        -> {- outerSig :: -}FunctionType
        -> {- innerSigs :: -}[FunctionType]{- length n -}
        -> CustomOp node
substOp parent outerSig innerSigs
  = CustomOp parent "BRAT" "Substitute" sig [toArg outerSig, TASequence (toArg <$> innerSigs)]
 where
  fnExts (FunctionType _ _ exts) = S.fromList exts
  combinedExts = S.toList $ foldr S.union (fnExts outerSig) (fnExts <$> innerSigs)

  sig = FunctionType (toFunc <$> (outerSig : innerSigs)) [toFunc outerSig] combinedExts
  toArg = TAType . HTFunc . PolyFuncType []

toFunc :: FunctionType -> HugrType
toFunc ty = HTFunc (PolyFuncType [] ty)

toSeq :: [HugrType] -> TypeArg
toSeq tys = TASequence (TAType <$> tys)

partialOp :: node  -- Parent
          -> FunctionType  -- Signature of the function that is partially evaluated
          -> Int  -- Number of arguments that are evaluated
          -> CustomOp node
partialOp parent funcSig numSupplied = CustomOp parent "BRAT" "Partial" sig args
 where
  sig :: FunctionType
  sig = FunctionType
        (toFunc funcSig : partialInputs)
        [toFunc (FunctionType otherInputs (output funcSig) (extensions funcSig))]
        ["BRAT"]
  args = [toSeq partialInputs, toSeq otherInputs, toSeq (output funcSig)]

  partialInputs = take numSupplied (input funcSig)
  otherInputs = drop numSupplied (input funcSig)


data LoadConstantOp node = LoadConstantOp
  { parent :: node
  , datatype :: HugrType
  } deriving (Eq, Functor, Show)

instance Eq node => Ord (LoadConstantOp node) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (LoadConstantOp node) where
  toJSON (LoadConstantOp {..}) = object ["parent" .= parent
                                        ,"op" .= ("LoadConstant" :: Text)
                                        ,"datatype" .= datatype
                                        ]

data LoadFunctionOp node = LoadFunctionOp
  { parent :: node
  , func_sig :: PolyFuncType
  , type_args :: [TypeArg]
  , signature :: FunctionType
  } deriving (Eq, Functor, Show)

instance Eq node => Ord (LoadFunctionOp node) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (LoadFunctionOp node) where
  toJSON (LoadFunctionOp {..}) = object ["parent" .= parent
                                        ,"op" .= ("LoadFunction" :: Text)
                                        ,"func_sig" .= func_sig
                                        ,"type_args" .= type_args
                                        ,"signature" .= signature
                                        ]

data NoopOp node = NoopOp
  { parent :: node
  , ty :: HugrType
  } deriving (Eq, Functor, Show)

instance Eq node => Ord (NoopOp node) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (NoopOp node) where
  toJSON (NoopOp {..}) = object ["parent" .= parent
                                ,"op" .= ("Noop" :: Text)
                                ,"ty" .= ty
                                ]

-- In the order they must be printed in - roots, inputs, outputs
data HugrOp node
  -- OpConditional should be compiled last so we can sort out its parent
  = OpMod (ModuleOp node)
  | OpIn (InputNode node)
  | OpOut (OutputNode node)
  -- the rest
  | OpDefn (FuncDefn node)
  | OpDFG (DFG node)
  | OpConst (ConstOp node)
  | OpConditional (Conditional node)
  -- Make sure that the cases are printed out in the correct order
  | OpCase (Int, Case node)
  | OpTag (TagOp node)
  | OpMakeTuple (MakeTupleOp node)
  | OpCustom (CustomOp node)
  | OpCall (CallOp node)
  | OpCallIndirect (CallIndirectOp node)
  | OpLoadConstant (LoadConstantOp node)
  | OpLoadFunction (LoadFunctionOp node)
  | OpNoop (NoopOp node)
 deriving (Eq, Functor, Ord, Show)

addMetadata :: [(String, String)] -> HugrOp node -> HugrOp node
addMetadata md (OpDFG (DFG { .. })) = OpDFG (DFG { metadata = metadata ++ md, .. })
addMetadata md (OpCase (i, (Case { .. }))) = OpCase (i, (Case { metadata = metadata ++ md, .. }))
addMetadata md (OpIn (InputNode { .. })) = OpIn (InputNode { metadata = metadata ++ md, .. })
addMetadata md (OpTag (TagOp { .. })) = OpTag (TagOp { metadata = metadata ++ md, .. })
addMetadata md (OpDefn (FuncDefn { .. })) = OpDefn (FuncDefn { metadata = metadata ++ md, .. })
addMetadata md (OpConditional (Conditional { .. })) = OpConditional (Conditional { metadata = metadata ++ md, .. })
addMetadata _ op = op

instance ToJSON node => ToJSON (HugrOp node) where
  toJSON (OpMod op) = toJSON op
  toJSON (OpDefn op) = toJSON op
  toJSON (OpConst op) = toJSON op
  toJSON (OpDFG op) = toJSON op
  toJSON (OpIn op) = toJSON op
  toJSON (OpOut op) = toJSON op
  toJSON (OpCase (_, op)) = toJSON op
  toJSON (OpConditional op) = toJSON op
  toJSON (OpTag op) = toJSON op
  toJSON (OpMakeTuple op) = toJSON op
  toJSON (OpCustom op) = toJSON op
  toJSON (OpCall op) = toJSON op
  toJSON (OpCallIndirect op) = toJSON op
  toJSON (OpLoadConstant op) = toJSON op
  toJSON (OpLoadFunction op) = toJSON op
  toJSON (OpNoop op) = toJSON op

getParent :: HugrOp node -> node
getParent (OpMod (ModuleOp { parent = parent })) = parent
getParent (OpDefn (FuncDefn { parent = parent })) = parent
getParent (OpConst (ConstOp { parent = parent })) = parent
getParent (OpDFG (DFG { parent = parent })) = parent
getParent (OpConditional (Conditional { parent = parent })) = parent
getParent (OpCase (_, Case { parent = parent })) = parent
getParent (OpIn (InputNode { parent = parent })) = parent
getParent (OpOut (OutputNode { parent = parent })) = parent
getParent (OpTag (TagOp { parent = parent })) = parent
getParent (OpMakeTuple (MakeTupleOp { parent = parent })) = parent
getParent (OpCustom (CustomOp { parent = parent })) = parent
getParent (OpCall (CallOp { parent = parent })) = parent
getParent (OpCallIndirect (CallIndirectOp { parent = parent })) = parent
getParent (OpLoadConstant (LoadConstantOp { parent = parent })) = parent
getParent (OpLoadFunction (LoadFunctionOp { parent = parent })) = parent
getParent (OpNoop (NoopOp { parent = parent })) = parent

data Hugr node = Hugr [HugrOp node] [(PortId node, PortId node)]
  deriving (Eq, Functor, Show)

instance ToJSON node => ToJSON (Hugr node) where
  toJSON (Hugr ns es) = object ["version" .= ("v1" :: Text)
                               ,"nodes" .= ns
                               ,"edges" .= es
                               ,"encoder" .= ("BRAT" :: Text)
                               ]

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
