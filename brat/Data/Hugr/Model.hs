{-# LANGUAGE OverloadedStrings, RecordWildCards #-}

module Data.Hugr.Model where

import Data.String (IsString(..))
import Data.Word (Word8)

--------------------------------------------------------------------------------
-----------------------------    Output format     -----------------------------
--------------------------------------------------------------------------------
-- Pretty printing structure: TODO actually do pretty printing
data Doc = Leaf String | Nowt | Doc :<> Doc | Line Int Doc

instance IsString Doc where
  fromString = Leaf

instance Semigroup Doc where
  Nowt <> b = b
  a <> Nowt = a
  a <> b = (a :<> b)

instance Monoid Doc where
  mempty = Nowt
  mappend = (<>)

printDoc :: Doc -> String
printDoc (Leaf str) = str
printDoc Nowt = ""
printDoc (a :<> b) = printDoc a ++ printDoc b
printDoc (Line n d) = "\n" ++ unlines ((replicate n ' ' ++) <$> lines (printDoc d))

parens :: Doc -> Doc
parens x = "(" <> x <> ")"

brackets :: Doc -> Doc
brackets x = "[" <> x <> "]"

doc :: String -> Doc
doc = Leaf

(</>) :: Doc -> Doc -> Doc
a </> Nowt = a
a </> b = a :<> (Line 0 b)

(<//>) :: Doc -> Doc -> Doc
a <//> Nowt = a
a <//> b = a :<> (Line 1 b)

(<+>) :: Doc -> Doc -> Doc
a <+> b = a :<> Leaf " " :<> b

concatLines :: [Doc] -> Doc
concatLines xs = foldr (flip (</>)) mempty xs

class Serialise t where
  serialise :: t -> Doc

--------------------------------------------------------------------------------
-----------------------------  Hugr model structs  -----------------------------
--------------------------------------------------------------------------------
data Package = H Module
type LinkName = String

instance Serialise Package where
  serialise (H hugr) = "(hugr 0)" <> Line 0 "(mod)" <> Line 0 (serialise hugr)

type Module = Region

data RegionKind = DFG | CFG | MOD

instance Serialise RegionKind where
  serialise DFG = "dfg"
  serialise CFG = "cfg"
  serialise MOD = "mod"

data Region = Region
  { kind :: RegionKind
  , sources :: [LinkName]
  , targets :: [LinkName]
  , children :: [Node]
  , regionMetas :: [Term]
  , regionSignature :: Maybe Term
  }

instance Serialise Region where
  serialise (Region { .. }) = "("
                              <> serialise kind
                              <+> printPortLists sources targets
                              <//> (printSignature regionSignature
                                    </> concatLines (printMeta <$> regionMetas)
                                    </> concatLines (serialise <$> children)
                                    )
                              <> ")"

data Visibility = Private | Public

instance Serialise Visibility where
  serialise Private = "private"
  serialise Public = "public"

data Param = Param String Term -- Term is the type of the param

instance Serialise Param where
  serialise (Param name ty) = "(param" <> doc name <> serialise ty <> ")"

type SymbolName = String

data Symbol = Symbol
  { vis :: Maybe Visibility
  , name :: SymbolName
  , params :: [Param]
  , constraints :: [Term]
  , symbolSig :: Term
  }

instance Serialise Symbol where
  serialise (Symbol { .. }) = mconcat
    [ maybe Nowt serialise vis
    , doc name
    , mconcat (serialise <$> params)
    , mconcat (serialise <$> constraints)
    , serialise symbolSig
    ]

data Operation
 = Invalid
 | Dfg
 | Cfg
 | Block
 | DefineFunc Symbol
 | DeclareFunc Symbol
 | Custom Term
 | DefineAlias Symbol Term
 | DeclareAlias Symbol
 | TailLoop
 | Conditional
 | DeclareConstructor Symbol
 | DeclareOperation Symbol
 | Import SymbolName

instance Serialise Operation where
  serialise op = case op of
    Invalid -> "invalid"
    Dfg -> "dfg"
    Cfg -> "cfg"
    Block -> "block"
    DefineFunc fn -> "define-func" <> serialise fn
    DeclareFunc fn -> "declare-func" <> serialise fn
    Custom tm -> serialise tm
    DefineAlias _ _ -> undefined
    DeclareAlias _ -> undefined
    TailLoop -> "tail-loop"
    Conditional -> "cond"
    DeclareConstructor con -> "declare-ctr" <> serialise con
    DeclareOperation op -> "declare-operation" <> serialise op
    Import name -> "import" <> doc name

data Node = Node
 { op :: Operation
 , inputs :: [LinkName]
 , outputs :: [LinkName]
 , regions :: [Region]
 , nodeMetas :: [Term]
 , nodeSignature :: Maybe Term
 }

printPortLists :: [LinkName] -> [LinkName] -> Doc
printPortLists [] [] = mempty
printPortLists ins outs = brackets (printList ins) <+> brackets (printList outs)
 where
  printList :: [LinkName] -> Doc
  printList xs = mconcat (doc <$> xs)

printSignature :: Maybe Term -> Doc
printSignature Nothing = mempty
printSignature (Just sig) = parens ("signature" <+> serialise sig)

printMeta :: Term -> Doc
printMeta x = "(meta " <> serialise x <> ")"

instance Serialise Node where
  serialise (Node { .. }) = "("
                            <> serialise op
                            <+> printPortLists inputs outputs
                            <//> (printSignature nodeSignature
                                  </> concatLines (printMeta <$> nodeMetas)
                                  </> concatLines (serialise <$> regions)
                                  )
                            <> ")"

data Term
 = Wildcard
 | Var String
 | Apply SymbolName [Term]
 | List [SeqPart]
 | Literal Literal
 | Tuple [SeqPart]
 | Func Region

instance Serialise Term where
   serialise Wildcard = "_"
   serialise (Var x) = doc x
   serialise (Apply sym []) = doc sym
   serialise (Apply sym tms) = parens (doc sym <+> (foldr1 (<+>) (serialise <$> tms)))
   serialise (List pts) = brackets (printListParts pts)
   serialise (Literal lit) = serialise lit -- TODO: Make Literal type
   serialise (Tuple pts) = parens (printTupleParts pts)
   serialise (Func region) = parens ("fn" <+> serialise region)

data SeqPart
 = Item Term
 | Splice(Term)

instance Serialise SeqPart where
   serialise (Item tm) = serialise tm
   serialise (Splice tm) = serialise tm <> "..."

printListParts :: [SeqPart] -> Doc
printListParts [Splice (List xs)] = printListParts xs
printListParts (Splice (List ys):xs) = printListParts ys <+> printListParts xs
printListParts [x] = serialise x
printListParts (x:xs) = serialise x <+> printListParts xs
printListParts [] = mempty

printTupleParts :: [SeqPart] -> Doc
printTupleParts (Splice (Tuple ys):xs) = printTupleParts ys <> printTupleParts xs
printTupleParts (x:xs) = serialise x <> printTupleParts xs
printTupleParts [] = mempty

data Literal
 = LitStr String
 | LitNat Int
 | LitBytes [Word8]
 | LitFloat Float
 deriving Show

instance Serialise Literal where
   serialise = \case
     LitStr str -> doc str
     LitNat n -> doc (show n)
     LitBytes bs -> parens ("bytes" <> printBytes bs)
     LitFloat flt -> doc (show flt)

printBytes :: [Word8] -> Doc
printBytes = undefined
