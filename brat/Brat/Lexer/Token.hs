module Brat.Lexer.Token (Tok(..), Token(..), Keyword(..), tokenLen) where

import Brat.FC

import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty(..))
import Text.Megaparsec (VisualStream(..))

data Tok
 = Ident String
 | QualifiedId (NonEmpty String) String
 | Equal
 | KindColon
 | TypeColon
 | PortColon
 | Hole String
 | Arrow
 | FatArrow
 | Lolly
 | LParen
 | RParen
 | LBrace
 | RBrace
 | LSquare
 | RSquare
 | Semicolon
 | Into
 | Comma
 | K Keyword
 | DotDot
 | Number Int
 | FloatLit Double
 | Comment String
 | Newline
 | Quoted String
 | Plus
 | Minus
 | Asterisk
 | Backslash
 | Slash
 | Caret
 | Hash
 | Dollar
 | Underscore
 | Pipe
 | Bang
 | Cons
 | Snoc
 | ConcatEqEven
 | ConcatEqOddL
 | ConcatEqOddR
 | Riffle
 | Percent
 deriving Eq

instance Show Tok where
  show (Ident s) = s
  show (QualifiedId (p :| ps) s) = intercalate "." (p:ps ++ [s])
  show Equal = "="
  show KindColon = "<-"
  show TypeColon = "::"
  show PortColon = ":"
  show (Hole h) = '?':h
  show Arrow = "->"
  show FatArrow = "=>"
  show Lolly = "-o"
  show LParen = "("
  show RParen = ")"
  show LBrace = "{"
  show RBrace = "}"
  show LSquare = "["
  show RSquare = "]"
  show Semicolon = ";"
  show Into = "|>"
  show Comma = ","
  show (K k) = show k
  show DotDot = ".."
  show (Number n) = show n
  show (FloatLit n) = show n
  show (Comment c) = "--" ++ c
  show Newline = "\n"
  show (Quoted x) = show x
  show Plus = "+"
  show Minus = "-"
  show Asterisk = "*"
  show Backslash = "\\"
  show Slash = "/"
  show Caret = "^"
  show Hash = "#"
  show Dollar = "$"
  show Underscore = "_"
  show Pipe = "|"
  show Bang = "!"
  show Cons = ",-"
  show Snoc = "-,"
  show ConcatEqEven = "=,="
  show ConcatEqOddL = "=,"
  show ConcatEqOddR = ",="
  show Riffle = "=%="
  show Percent = "%"

data Token = Token { fc :: FC
                   , _tok :: Tok
                   }
instance Eq Token where
  (Token fc t) == (Token fc' t') = t == t' && fc == fc'

instance Show Token where
  show (Token _ t) = show t

instance Ord Token where
  compare (Token (FC st nd) _) (Token (FC st' nd') _) = if st == st'
                                                        then compare nd nd'
                                                        else compare st st'

data Keyword
  = KType
  | KExt
  | KImport
  | KLet
  | KIn
  | KOf
  deriving Eq

instance Show Keyword where
  show KType = "type"
  show KExt = "ext"
  show KImport = "import"
  show KLet = "let"
  show KIn = "in"
  show KOf = "of"

tokLen :: Tok -> Int
tokLen = length . show

tokenLen = tokLen . _tok

instance VisualStream [Token] where
  tokensLength _ = sum . fmap (\(Token _ t) -> tokLen t)
  showTokens _ = concatMap show
