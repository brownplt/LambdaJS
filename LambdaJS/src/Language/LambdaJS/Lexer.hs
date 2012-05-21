module Language.LambdaJS.Lexer
  ( lexeme
  , identifier
  , reserved
  , reservedOp
  , float
  , integer
  , stringLiteral
  , braces
  , parens
  , comma
  , colon
  , semi
  , squares
  ) where

import Prelude hiding (lex)
import Text.Parsec
import Text.Parsec.Token (GenLanguageDef (..))
import qualified Text.Parsec.Token as T

def = T.LanguageDef { 
  commentStart = "/*",
  commentEnd = "*/",
  commentLine = "//",
  nestedComments = True,
  identStart = letter <|> oneOf "$_@",
  identLetter = alphaNum <|> oneOf "$_-><",
  opStart = oneOf "{}<>()~.,?:|&^=!+-*/%![]",
  opLetter = oneOf "=<>|&+",
  reservedNames = [ "true", "false", "fun", "let", "in", "and", "ref",
                    "delete", "if", "then", "else", "while", "do", "label",
                    "break", "throw", "try", "catch", "finally", "typeof", 
                    "op" ],
  reservedOpNames = [ ".", ",", "{", "}", "(", ")", "=", ":=", "!", "[", "]",
                      ";", "&&", "||" ],
  caseSensitive = False
}

lex :: T.TokenParser st
lex = T.makeTokenParser def

-- everything but commaSep and semiSep
identifier = T.identifier  lex
reserved = T.reserved lex
operator = T.operator lex
reservedOp = T.reservedOp lex 
charLiteral = T.charLiteral lex 
stringLiteral = T.stringLiteral lex 
natural = T.natural lex 
integer = T.integer lex 
float = T.float lex 
naturalOrFloat = T.naturalOrFloat lex 
decimal = T.decimal lex 
hexadecimal = T.hexadecimal lex 
octal = T.octal lex 
symbol = T.symbol lex 
whiteSpace = T.whiteSpace lex 
parens = T.parens  lex
braces = T.braces  lex
squares = T.squares lex 
semi = T.semi  lex
comma = T.comma  lex
colon = T.colon lex 
dot = T.dot lex
brackets = T.brackets lex
lexeme = T.lexeme lex
