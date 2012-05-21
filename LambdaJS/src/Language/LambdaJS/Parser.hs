module Language.LambdaJS.Parser
  ( parseBinds
  ) where

import Prelude hiding (id, break, undefined, null, seq)
import Language.LambdaJS.Lexer
import Text.Parsec hiding (label, string)
import Text.Parsec.Expr
import Language.LambdaJS.Syntax hiding (label)
import Language.LambdaJS.PrettyPrint (opReps)
import Control.Monad
import Debug.Trace

right p lst = do
  let f e = do { e' <- choice (map (\g -> g e) lst); f e' } <|> (return e)
  init <- p
  f init

number = do
  p <- getPosition
  n <- float <|> (liftM fromIntegral integer)
  return (ENumber p n)

string = liftM2 EString getPosition stringLiteral

bool = liftM2 EBool getPosition (true <|> false)
  where true = reserved "true" >> return True
        false = reserved "false" >> return False

undefined = reserved "undefined" >> (liftM EUndefined getPosition)

null = reserved "null" >> (liftM ENull getPosition)
 
lambda = do
  p <- getPosition
  reserved "fun"
  args <- parens (identifier `sepBy` comma)
  reservedOp "."
  body <- expr
  return (ELambda p args body)

object = do
  p <- getPosition
  let field = do
        x <- stringLiteral
        colon
        e <- expr
        return (x, e)
  fields <- braces (field `sepBy` comma)
  return (EObject p fields)

id = liftM2 EId getPosition identifier

app f = do
  p <- getPosition
  args <- parens (expr `sepBy` comma)
  return (EApp p f args)

let_ = do
  p <- getPosition
  reserved "let"
  let bind = do
        x <- identifier
        reservedOp "="
        e <- expr
        return (x, e)
  binds <- bind `sepBy1` (reserved "and")
  reserved "in"
  body <- expr
  return (ELet p binds body)

ref = do
  p <- getPosition
  reserved "ref"
  e <- atom
  return (ERef p e)

deref = do
  p <- getPosition
  reservedOp "!"
  e <- atom
  return (EDeref p e)

typeof = do
  p <- getPosition
  reserved "typeof"
  e <- atom
  return (EOp p OTypeof [e])

getUpdateField e1 = do
  p <- getPosition
  reservedOp "["
  e2 <- expr
  let upd = do
        reservedOp ":=" 
        e3 <- expr
        reservedOp "]" <?> "closing bracket"
        return (EUpdateField p e1 e2 e3)
  let get = do
        reservedOp "]"
        return (EGetField p e1 e2)      
  upd <|> get

deleteField = do
  p <- getPosition
  reserved "delete"
  e1 <- term
  e2 <- squares expr
  return (EDeleteField p e1 e2)


if_ = do
  p <- getPosition
  reserved "if"
  e1 <- expr
  reserved "then"
  e2 <- expr
  reserved "else"
  e3 <- expr
  return (EIf p e1 e2 e3)

while = do
  p <- getPosition
  reserved "while"
  e1 <- expr
  reserved "do"
  e2 <- expr
  return (EWhile p e1 e2)


break = do
  p <- getPosition
  reserved "break"
  x <- identifier
  e <- expr
  return (EBreak p x e)

throw = do
  p <- getPosition
  reserved "throw"
  e <- expr
  return (EThrow p e)

tryCatchFinally = do
  p <- getPosition
  reserved "try"
  e1 <- expr
  let catch = do
        reserved "catch"
        e2 <- expr
        return (ECatch p e1 e2)
  let finally = do
        reserved "finally"
        e2 <- expr
        return (EFinally p e1 e2)
  catch <|> finally

label = do
  p <- getPosition
  reserved "label"
  x <- identifier
  colon
  e <- expr
  return (ELabel p x e)

setref = Infix parser AssocRight
  where parser = do
          p <- getPosition
          reservedOp ":="
          return (\e1 e2 -> ESetRef p e1 e2)

infixExpr str constr = Infix parser AssocLeft
  where parser = do
          p <- getPosition
          reservedOp str
          return (\e1 e2 -> EOp p constr [e1, e2])

andMacro = Infix parser AssocLeft
  where parser = do
          p <- getPosition
          reservedOp "&&"
          return (\e1 e2 -> EIf p e1 e2 (EBool p False))

orMacro = Infix parser AssocLeft
  where parser = do
          p <- getPosition
          reservedOp "||"
          return (\e1 e2 -> EIf p e1 (EBool p True) e2)

exprTable =
  [ [ infixExpr "===" OStrictEq ],
    [ andMacro, orMacro ],
    [ setref ] ]


atom = string <|> id <|> deref <|> parens expr <|> number <|> bool <|> 
         undefined <|> null <|> object <|> typeof <|> ref

term = buildExpressionParser exprTable atom

expr' = right term [ app, getUpdateField ]
  

operator =
  let tbl = map (\(op,str) -> do { reserved str; return op }) opReps 
    in choice tbl

op = do
  p <- getPosition
  reserved "op"
  reservedOp "("
  name <- operator
  reservedOp ","
  args <- expr `sepBy` comma
  reservedOp ")"
  return (EOp p name args)

expr = chainr1 exp seq
  where exp = if_ <|> while <|> deleteField <|>  tryCatchFinally <|> 
                label <|> break <|> lambda <|> let_ <|> throw <|>
                op <|> expr'
        seq = do
          p <- getPosition
          semi
          return (ESeq p)

parseBinds :: String -- ^source name
           -> String -- ^source text
           -> Either ParseError (Expr SourcePos -> Expr SourcePos)
parseBinds name src = 
  let parseOne = do
        reserved "let"
        x <- identifier
        reservedOp "="
        e <- expr
        return (x, e)
      parser = do
        p <- getPosition
        binds <- many parseOne
        eof
        let fn body = foldr (\(x, e) body -> ELet p [(x, e)] body) body binds
        return fn
    in parse parser name src
      

