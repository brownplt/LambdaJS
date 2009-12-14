module Main where

import BrownPLT.JavaScript.Semantics.Desugar
import Control.Monad
import BrownPLT.JavaScript.Semantics.Syntax
import BrownPLT.JavaScript.Semantics.RemoveHOAS
import BrownPLT.JavaScript.Semantics.PrettyPrint
import qualified Data.Map as M
import qualified Data.Set as S
import Debug.Trace
import MakeSafeSubset
import Control.Monad.State
import Data.Either
import Data.List


type Env = M.Map Ident T


data T = TSafeString | TSafe | JS deriving (Show, Eq, Ord)


subType x y | x == y = True
subType TSafe JS = True
subType TSafeString TSafe = True
subType TSafeString JS = True
subType _ _ = False


superType t1 t2 = case t1 `compare` t2 of
  LT -> t2
  GT -> t1
  EQ -> t1

instance Monad (Either String) where
  return x = Right x
  fail s = Left s
  (Right x) >>= f = f x
  (Left s) >>= _ = Left s


typeCheck :: Env -> Expr -> Either String T
typeCheck env e = case e of
   ENumber _ -> return TSafe
   EString "XMLHttpRequest" -> return JS
   EString _ -> return TSafe
   EUndefined -> return TSafe
   EBool _ -> return TSafe
   ENull -> return TSafe
   ELambda xs e -> do
     let env' = M.fromList (map (\x -> (x, JS)) xs)
     typeCheck (M.union env' env) e
     return TSafe
   EId x -> case M.lookup x env of
     Just t -> return t
     Nothing -> error $ "unbound identifier: " ++ x
   ELet binds body -> do
     boundTypes <- mapM (typeCheck env) (map snd binds)
     let env' = M.fromList $ zip (map fst binds) boundTypes
     typeCheck (M.union env' env) body
   EDeref e -> do
     t <- typeCheck env e
     return JS
   EDeleteField e1 e2 -> do
     typeCheck env e1
     typeCheck env e2
     return JS
   ESetRef e1 e2 -> do
     typeCheck env e1
     typeCheck env e2
     return JS
   ERef e -> do
     t <- typeCheck env e
     return TSafe
   EApp e es -> do
     ts <- mapM (typeCheck env) (e:es)
     case all (\t -> subType t JS) ts of
       True -> return JS
       False -> fail "EApp expects all arguments to be subtypes of JS"
   ESeq e1 e2 -> do
     t1 <- typeCheck env e1
     typeCheck env e2
   EOp OPrimToStr [e] -> do
     typeCheck env e
   -- Other primitives are effectively uninterpreted.  Primitives produce
   -- constants (and constant-carrying objects).  Therefore, they cannot
   -- introduce locations.
   EOp _ es -> do
     ts <- mapM (typeCheck env) es
     return JS
   EIf (EOp OStrictEq [EOp OTypeof [EId x], EString "location"]) e2 e3
     | M.lookup x env == Just TSafeString  ->
     typeCheck env e3
   EIf (EOp OStrictEq [EOp OTypeof [EId x], EString "string"]) e2 e3 
     | M.lookup x env == Just TSafe -> do
    t2 <- typeCheck (M.insert x TSafeString env) e2
    t3 <- typeCheck env e3
    return (superType t2 t3)
   EIf (EOp OStrictEq [EId x,EString "XMLHttpRequest"]) e2 e3 -> do
     case M.lookup x env of
       Nothing -> error "unbound id"
       Just _ -> do
         t2 <- typeCheck env e2
         t3 <- typeCheck (M.insert x TSafe env) e3
         return (superType t2 t3)
   EIf e1 e2 e3 -> do
     t1 <- typeCheck env e1
     t2 <- typeCheck env e2
     t3 <- typeCheck env e3
     return (superType t2 t3)
   EObject props -> do
     ts <- mapM (typeCheck env) (map snd props)
     return TSafe
   EGetField e1 e2 -> do
     t1 <- typeCheck env e1
     t2 <- typeCheck env e2
     case t2 of
       TSafe -> return JS
       TSafeString -> return JS
       otherwise -> fail $ "unsafe field lookup.\n" ++ 
                           "type of field is " ++ 
                           show (M.lookup "field" env) ++
                           "\n" ++
                           (pretty e2)
   EUpdateField e1 e2 e3 -> do
     t1 <- typeCheck env e1
     t2 <- typeCheck env e2
     t3 <- typeCheck env e3
     return JS
   ELabel lbl e -> typeCheck env e -- TODO : wrong
   EBreak lbl e -> typeCheck env e -- TODO : wrong
   EThrow e -> typeCheck env e
   ELet1{} -> error "unexpected ELet1 (removeHOAS not called?)"
   ELet2{} -> error "unexpected ELet2 (removeHOAS not called?)"
   EWhile e1 e2 -> do
     typeCheck env e1
     typeCheck env e2
     return JS
   ECatch e1 e2 -> do
     typeCheck env e1
     typeCheck env e2
     return JS
   EFinally e1 e2 -> do
     typeCheck env e1
     typeCheck env e2
     return JS


isTypeable = typeCheck M.empty . removeHOAS


safeSubset = (safeExprs ++ safeStmts, unsafeExprs ++ unsafeStmts)
  where (safeExprs, unsafeExprs) = safeExpressions isTypeable
        (safeStmts, unsafeStmts) = safeStatements isTypeable

safeLookup = 
  "function(obj, field)  { \n\
  \  if (field === \"XMLHttpRequest\") { \n\
  \    return undefined; \n\
  \  } \n\
  \  else if (typeof field === \"string\") { \n\
  \    return obj[field]; \n\
  \  } \n\
  \  else { \n\
  \    return undefined; \n\
  \  } }"


main = do
  let (safe, unsafe) = safeSubset
  putStrLn "Safe Forms"
  putStrLn "=========="
  putStrLn (concat $ intersperse "\n" safe)
  putStrLn ""
  putStrLn "Unsafe Forms"
  putStrLn "============"
  putStrLn (concat $ intersperse "\n" unsafe)
  putStrLn ""
  putStrLn "lookup is defined as:"
  putStrLn safeLookup
  putStrLn ""
  case check isTypeable [] safeLookup of
    Right  _ -> putStrLn "lookup is typable."
    Left err -> putStrLn err
  
{-  putStrLn $ pretty $
    desugarExpr (parseExpr "obj[field] = e") 
             (\body -> ELet (map (\x -> (x, EUndefined)) globalEnv) $ 
                       ELet (map (\x -> (x, EUndefined)) ["obj", "field", "e"]) $
                         body)

 
-}