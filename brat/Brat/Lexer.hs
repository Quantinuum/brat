module Brat.Lexer (lex) where

import Prelude hiding (lex)

import Brat.Lexer.Flat (lexFlat)

lex = lexFlat
