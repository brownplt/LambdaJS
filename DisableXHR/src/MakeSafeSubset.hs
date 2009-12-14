module MakeSafeSubset
  ( safeExpressions
  , safeStatements
  , globalEnv
  , parseExpr
  , check
  ) where

import BrownPLT.JavaScript.Syntax
import qualified Data.Map as M
import qualified BrownPLT.JavaScript.Parser as P
import BrownPLT.JavaScript.Semantics.Syntax
import BrownPLT.JavaScript.Semantics.Desugar
import BrownPLT.JavaScript.Semantics.ECMAEnvironment
import Text.ParserCombinators.Parsec (parse)
import Data.Maybe
import Data.List


parseExpr str = case parse P.parseExpression "MakeSafeSubset.hs" str of
  Left err -> error (show err)
  Right e -> e

parseStmt str = case parse P.parseStatement "MakeSafeSubset.hs" str of
  Left err -> error (show err)
  Right e -> e


globalEnv =
  [ "$global", "$Object.prototype", "$Function.prototype", "$Date.prototype"
  , "$Number.prototype", "$Array.prototype", "$Boolean.prototype"
  , "$Error.prototype", "$Boolean.prototype", "$Error.prototype" 
  , "$ConversionError.prototype", "$RangeError.prototype" 
  , "$ReferenceError.prototype", "$SyntaxError.prototype" 
  , "$TypeError.prototype", "$URIError.prototype", "Object", "Function"
  , "Array", "$RegExp.prototype", "RegExp", "Date", "Number"
  , "$String.prototype", "String", "Boolean", "Error", "ConversionError"
  , "EvalError", "RangeError", "ReferenceError", "SyntaxError", "TypeError"
  , "uRIError", "this", "$makeException"
  ]



check :: (Expr -> Either String typ) -> [Ident] -> String
      -> Either String String
check typeCheck freeIds src = 
  let expr = desugarExpr (parseExpr src) 
             (\body -> ELet (map (\x -> (x, EUndefined)) globalEnv) $ 
                       ELet (map (\x -> (x, EUndefined)) freeIds) $
                         body)
    in case typeCheck expr of
         Right _ -> Right src
         Left err -> Left err

checkStmt typeCheck freeIds src = 
  let expr = desugarStmt (parseStmt src) 
             (\body -> ELet (map (\x -> (x, EUndefined)) globalEnv) $ 
                       ELet (map (\x -> (x, EUndefined)) freeIds) $
                         body)
    in case typeCheck expr of
         Right _ -> Right src
         Left err -> Left err


removeIdents (xs, ys) = (map snd xs, map snd ys)
      

safeExpressions :: (Expr -> Either String typ)
               -> ([String], [String])
safeExpressions tc =  removeIdents (partition f allExprs)
  where f (xs, e) = case check tc xs e of
                      Right _ -> True
                      Left _ -> False

safeStatements tc = removeIdents (partition f statements)
  where f (xs, e) = case checkStmt tc xs e of
                      Right _ -> True
                      Left _ -> False



allExprs :: [([Ident], String)]
allExprs = infixOps ++ assignOps ++ prefixOp ++ unaryAssignOp ++ others


others = 
  [ ([], "this") 
  , (["obj", "e"], "obj.field = e")
  , (["obj", "field", "e"], "obj[field] = e") 
  -- There isn't a good, generic way to mechanize this.  To disable access to
  -- different properties, we have to explicitly enumerate which dotted field
  -- accesses are disallowed.
  , (["obj"], "obj.x")
  , (["obj"], "obj.XMLHttpRequest")
  , (["obj", "field"], "obj[field]")
  , (["obj", "arg"], "new obj(arg)")
  , (["e1", "e2", "e3"], "e1 ? e2 : e3")
  , (["f", "arg"], "f(arg)")
  , (["f", "arg"], "new f(arg)")
  , (["e1", "e2"], "{ x: e1, y: e2 }")
  , (["body"], "function(x) { body }")
  , (["obj", "field"], "obj[field]++")
  , (["obj", "field"], "obj[field]--")
  , (["obj", "field"], "++obj[field]")
  , (["obj", "field"], "--obj[field]")
  , (["e1", "e2", "e3"], "e1 ? e2 : e3")
  ]

statements =
  [
    (["s1", "s2"], "{ s1 ; s2 }")
  , (["e1", "s1"], "if (e1) { s1 }")
  , (["e1", "s1", "s2"], "if (e1) { s1 } else { s2 } ")   
  , (["e", "s1", "s2"], "switch (e1) { case foo: s1\n case bar: s2 }")
  , (["e1", "s1"], "while (e1) { s1 }")
  -- TODO: ADD desguaring , (["e1", "s1"], "do { s1 } while (e1)")
  , ([], "break lbl")
  , ([], "break")
  , ([], "continue lbl")
  , ([], "continue")
  , (["s"], "myLabel: s")
  , (["e", "s"], "for (var x in e) { s }")
  , (["e", "s"], "for (x in e) { s }")
  , (["x", "e1", "e2", "e3", "s"], "for (var x = e1; e2; e3) { s }")
  , (["s1", "s2"], "try { s1 } catch(x) { s2 }")
  , (["s1", "s2"], "try { s1 } finally { s2 }")
  , (["e"], "throw e")
  , (["e"], "return e")
  -- Do *not* include with.  It is nonsensical given our theory.
  , (["e"], "var x = e")
  ]


-- TODO: missing OpIn, because we haven't implemented desugaring for in.
infixOps = map (\s -> (["x", "y"],s)) $
  [ "x < y", "x <= y", "x > y", "x >= y", "x instanceof y", "x == y", "x != y"
  , "x === y", "x !== y", "x && y", "x || y", "x * y", "x / y", "x % y"
  , "x - y", "x << y", "x >> y", "x >>> y", "x & y", "x ^ y", "x | y", "x + y"
  ]

assignOps = map (\s -> (["x", "y"],s)) $
  [ "x = y", "x += y", "x -= y", "x *= y", "x /= y", "x %= y", "x <<= y"
  , "x >>= y", "x >>>= y", "x &= y", "x ^= y", "x |= y"
  ]

unaryAssignOp = map (\s -> (["x"],s)) $
  [ "++x", "--x", "x++", "x--" ]

prefixOp = map (\s -> (["x"],s)) $
  [ "!x", "~x", "+x", "-x", "typeof x", "void x", "delete x" ]
