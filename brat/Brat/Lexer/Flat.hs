module Brat.Lexer.Flat (lexFlat) where

import Prelude hiding (lex)
import Data.Char (isSpace)
import Data.Functor (($>), void)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Void
import Text.Megaparsec hiding (Token, Pos, token, State, between)
import Text.Megaparsec.Char hiding (space)

import Brat.FC
import Brat.Lexer.Token

readL :: Read a => String -> Lexer a
readL x = case reads x of
            ((v, _):_) -> pure v
            _ -> fail ("readL failed on input " ++ x)

type Lexer a = Parsec Void String a

keyword :: Lexer Keyword
keyword
  = ((try (string "type") $> KType)
     <|> string "ext"   $> KExt
     <|> string "import" $> KImport
     <|> string "let" $> KLet
     <|> string "in" $> KIn
     <|> string "of" $> KOf
    ) <* notFollowedBy identChar

identChar :: Lexer Char
identChar = alphaNumChar <|> oneOf "_'"

ident :: Lexer String
ident = (<?> "name") $ do
  a <- letterChar
  bc <- many identChar
  pure (a:bc)

qualified :: Lexer Tok
qualified = (<?> "qualified name") $ do
  first <- ident <* string "."
  rest  <- many (try $ ident <* string ".")
  QualifiedId (first :| rest) <$> ident

space :: Lexer ()
space = many ((satisfy isSpace >> return ()) <|> comment) >> return ()
 where
  comment :: Lexer ()
  comment = string "--" *> ((printChar `manyTill` lookAhead (void newline <|> void eof)) >> return ())

tok :: Lexer Tok
tok = try (char '(' $> LParen)
      <|> try (char ')' $> RParen)
      <|> try (char '{' $> LBrace)
      <|> try (char '}' $> RBrace)
      <|> try (char '[' $> LSquare)
      <|> try (char ']' $> RSquare)
      <|> try (Underscore <$ string "_")
      <|> try (Quoted <$> (char '"' *> printChar `manyTill` char '"'))
      <|> try (FloatLit <$> float)
      <|> try (Number <$> number)
      <|> try (string "+" $> Plus)
      <|> try (string "/" $> Slash)
      <|> try (string "\\" $> Backslash)
      <|> try (string "^" $> Caret)
      <|> try (string "->") $> Arrow
      <|> try (string "=>") $> FatArrow
      <|> try (string "-o") $> Lolly
      <|> try (Hole <$> (char '?' *> ident))
      <|> try (string "::" $> TypeColon)
      <|> try (char ':' $> PortColon)
      <|> try (char ';' $> Semicolon)
      <|> try (string "|>" $> Into)
      <|> try (string ",-" $> Cons)
      <|> try (string "-," $> Snoc)
      <|> try (string "=,=" $> ConcatEqEven)
      <|> try (string "=," $> ConcatEqOddL)
      <|> try (string ",=" $> ConcatEqOddR)
      <|> try (string "=%=" $> Riffle)
      <|> try (char '=' $> Equal)
      <|> try (char ',' $> Comma)
      <|> try (string ".." $> DotDot)
      <|> try (string "<-" $> KindColon)
      <|> try (string "#"  $> Hash)
      <|> try (string "*"  $> Asterisk)
      <|> try (string "-" $> Minus)
      <|> try (string "$" $> Dollar)
      <|> try (string "|" $> Pipe)
      <|> try (string "!" $> Bang)
      <|> try (string "%" $> Percent)
      <|> try (K <$> try keyword)
      <|> try qualified
      <|> Ident <$> ident
 where
  float :: Lexer Double
  float = label "float literal" $ do
    n <- some digitChar
    char '.'
    m <- some digitChar
    let val = n ++ "." ++ m
    readL val

  number :: Lexer Int
  number = label "number literal" $ do
    val <- some digitChar
    readL val

en :: Lexer Tok -> Lexer Token
en l = do st <- convPos <$> getSourcePos
          x <- l
          nd <- convPos <$> getSourcePos
          pure $ Token (FC st nd) x

token :: Lexer Token
token = space >> en tok

convPos :: SourcePos -> Pos
convPos (SourcePos _ l c) = Pos (unPos l) (unPos c)

lexFlat :: Lexer [Token]
lexFlat = token `manyTill` try (space >> eof)
