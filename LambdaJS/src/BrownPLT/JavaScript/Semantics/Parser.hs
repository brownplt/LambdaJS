module BrownPLT.JavaScript.Semantics.Parser where

import Control.Applicative ( Applicative(..), (<$>))
import Control.Monad

import Data.Set ( Set )
import qualified Data.Set as S

import BrownPLT.JavaScript.Semantics.Syntax
import BrownPLT.JavaScript.Lexer

import Text.ParserCombinators.Parsec

instance Applicative (GenParser tok st) where
  pure    = return
  f <*> a = f `ap` a

withPos :: (SourcePos -> a) -> CharParser st a
withPos c = c <$> getPosition

(<@>) :: (SourcePos -> a -> b) -> CharParser st a -> CharParser st b
(<@>) c p = (withPos c) <*> p
infixl 4 <@>

(<@->) :: (SourcePos -> a) -> CharParser st b -> CharParser st a
(<@->) c p = (withPos (\p _ -> c p)) <*> p
infixl 4 <@->

-- Note that some of these keywords are not keywords in JavaScript. If we're
-- parsing desugared JavaScript code, these maybe used as identifiers in that
-- code. It's exactly for this reason that 'object' is not included in the list
-- below, since it's used as a variable name in ADsafe.
--
-- tldr: 'object' is not included in this list so the parser works with ADsafe.
--
keywords :: Set String
keywords = S.fromList $
    [ "let", "lambda", "alloc", "deref", "begin"
    , "if", "while", "label", "break", "throw", "null", "undefined"
    ]

lstring = lexeme . string
ident' = lexeme $ do 
    c <- letter <|> oneOf "$_"
    cs <- many (alphaNum <|> oneOf "$_.")
    return (c:cs)

ident = do
  id <- ident'
  if id `S.member` keywords
    then fail $ id ++ " is a reserved keyword"
    else return id

op :: CharParser st Op 
op = (lexeme $ (string "+" >> return ONumPlus)
  <|> (try $ string "string-+" >> return OStrPlus)
  <|> (string "*" >> return OMul)
  <|> (string "/" >> return ODiv)
  <|> (string "%" >> return OMod)
  <|> (string "-" >> return OSub)
  <|> (try $ string "<" >> return OLt)
  <|> (try $ string "string-<" >> return OStrLt)
  <|> (try $ string "===" >> return OStrictEq)
  <|> (string "==" >> return OAbstractEq)
  <|> (try $ string "typeof" >> return OTypeof)
  <|> (try $ string "surface-typeof" >> return OSurfaceTypeof)
  <|> (try $ string "prim->number" >> return OPrimToNum)
  <|> (try $ string "prim->string" >> return OPrimToStr)
  <|> (try $ string "prim->bool" >> return OPrimToBool)
  <|> (try $ string "prim?" >> return OIsPrim)
  <|> (try $ string "to-integer" >> return OToInteger)
  <|> (try $ string "to-int-32" >> return OToInt32)
  <|> (try $ string "to-uint-32" >> return OToUInt32)
  <|> (string "&" >> return OBAnd)
  <|> (string "\\|" >> return OBOr)
  <|> (string "^" >> return OBXOr)
  <|> (string "~" >> return OBNot)
  <|> (try $ string "<<" >> return OLShift)
  <|> (try $ string ">>" >> return OSpRShift)
  <|> (string ">>>" >> return OZfRShift)
  <|> (try $ string "has-own-prop?" >> return OHasOwnProp)
  <|> (try $ string "print-string" >> return OPrint)
  <|> (try $ string "str-contains" >> return OStrContains)
  <|> (try $ string "obj-iterate-has-next?" >> return OObjIterHasNext)
  <|> (try $ string "obj-iterate-next" >> return OObjIterNext)
  <|> (try $ string "obj-iterate-key" >> return OObjIterKey)
  <|> (try $ string "str-startswith" >> return OStrStartsWith)
  <|> (try $ string "str-length" >> return OStrLen)
  <|> (try $ string "str-split-regexp" >> return OStrSplitRegExp)
  <|> (try $ string "str-split-strexp" >> return OStrSplitStrExp)
  <|> (try $ string "obj-can-delete?" >> return OObjCanDelete)
  <|> (try $ string "math-exp" >> return OMathExp)
  <|> (try $ string "math-log" >> return OMathLog)
  <|> (try $ string "math-cos" >> return OMathCos)
  <|> (try $ string "math-sin" >> return OMathSin)
  <|> (try $ string "math-abs" >> return OMathAbs)
  <|> (try $ string "math-pow" >> return OMathPow)
  <|> (try $ string "regexp-quote" >> return ORegExpQuote)
  <|> (try $ string "regexp-match" >> return ORegExpMatch))
  <?> "op"

value :: CharParser st (Expr SourcePos)
value = ((ENumber <@> float) 
        <|> (EString    <@>  stringLiteral)
        <|> (EBool      <@>  bool)
        <|> (try $ EId  <@>  ident)
        <|> (EUndefined <@-> lstring "undefined")
        <|> (ENull      <@-> lstring "null")
        <|> (EEval      <@-> lstring "eval-semantic-bomb"))
        <?> "value"
  where 
    bool = string "#" >> 
            ((lstring "t" >> return True) <|> (lstring "f" >> return False))

args = parens (many ident)

assoc :: CharParser st (String, Expr SourcePos)
assoc = parens $ do { k <- stringLiteral; v <- expr; return (k, v) }

clause :: CharParser st (Ident, Expr SourcePos)
clause = parens $ do { k <- ident; v <- expr; return (k, v) }

expr :: CharParser st (Expr SourcePos)
expr = (try value)
  <|> (parens $
            (ELet         <@-> (try $ lstring "let")          <*> clauses <*> expr)
        <|> (ELambda      <@-> (try $ lstring "lambda")       <*> args <*> expr)
        <|> (EObject      <@-> (try $ lstring "object")       <*> (many assoc))
        <|> (ESetRef      <@-> (try $ lstring "set!")         <*> ident <*> expr)
        <|> (ERef         <@-> (try $ lstring "alloc")        <*> expr)
        <|> (EDeref       <@-> (try $ lstring "deref")        <*> expr)
        <|> (EGetField    <@-> (try $ lstring "get-field")    <*> expr  <*> expr)
        <|> (EUpdateField <@-> (try $ lstring "update-field") <*> expr  <*> expr <*> expr)
        <|> (EDeleteField <@-> (try $ lstring "delete-field") <*> expr  <*> expr)
        <|> (ESeq         <@-> (try $ lstring "begin")        <*> expr  <*> expr)
        <|> (EIf          <@-> (try $ lstring "if")           <*> expr  <*> expr <*> expr)
        <|> (EWhile       <@-> (try $ lstring "while")        <*> expr  <*> expr)
        <|> (ELabel       <@-> (try $ lstring "label")        <*> ident <*> expr)
        <|> (EBreak       <@-> (try $ lstring "break")        <*> ident <*> expr)
        <|> (EThrow       <@-> (try $ lstring "throw")        <*> expr)
        <|> (ECatch       <@-> (try $ lstring "try-catch")    <*> expr  <*> expr)
        <|> (EFinally     <@-> (try $ lstring "try-finally")  <*> expr  <*> expr)
        <|> (EOp          <@>  (try $ op) <*> (many expr))
        <|> (EApp         <@>  expr       <*> (many expr)))
  where clauses = parens $ many clause
