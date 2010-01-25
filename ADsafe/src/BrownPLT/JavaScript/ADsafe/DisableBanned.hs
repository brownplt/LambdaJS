module BrownPLT.JavaScript.ADsafe.DisableBanned ( typeCheck ) where

import Data.Map ( Map )
import qualified Data.Map as M
import Data.Set ( Set )
import qualified Data.Set as S

import BrownPLT.JavaScript.Semantics.Syntax
import BrownPLT.JavaScript.Semantics.RemoveHOAS ( removeHOAS )
import BrownPLT.JavaScript.Semantics.PrettyPrint ( pretty )


type Env = Map Ident T

data T = SafeString | Safe | JS
  deriving ( Show, Eq, Ord )


subType x y | x == y = True
subType Safe JS = True
subType SafeString Safe = True
subType SafeString JS = True
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


-- ADsafe banned list
banned :: Set String
banned = 
  S.fromList [ "arguments", "callee", "caller", "constructor", "eval"
             , "prototype", "unwatch", "valueOf", "watch" ]

typeCheck :: Env -> ExprPos -> Either String T
typeCheck env e = case e of
   ENumber _ _  -> return Safe
   EString _ s  -> return $ if s `S.member` banned then JS else Safe
   EUndefined _ -> return Safe
   EBool _ _    -> return Safe
   ENull _ -> return Safe
   ELambda _ xs e -> do
     let env' = M.fromList (map (\x -> (x, JS)) xs)
     typeCheck (M.union env' env) e
     return Safe
   EId _ x -> case M.lookup x env of
     Just t -> return t
     Nothing -> error $ "unbound identifier: " ++ x
   ELet _ binds body -> do
     boundTypes <- mapM (typeCheck env) (map snd binds)
     let env' = M.fromList $ zip (map fst binds) boundTypes
     typeCheck (M.union env' env) body
   EDeref _ e -> do
     t <- typeCheck env e
     return JS
   EDeleteField _ e1 e2 -> do
     typeCheck env e1
     typeCheck env e2
     return JS
   ESetRef _ e1 e2 -> do
     typeCheck env e1
     typeCheck env e2
     return JS
   ERef _ e -> do
     t <- typeCheck env e
     return Safe
   EApp _ e es -> do
     ts <- mapM (typeCheck env) (e:es)
     case all (\t -> subType t JS) ts of
       True -> return JS
       False -> fail "EApp expects all arguments to be subtypes of JS"
   ESeq _ e1 e2 -> do
     t1 <- typeCheck env e1
     typeCheck env e2
   EOp _ OPrimToStr [e] -> do
     typeCheck env e
   -- Other primitives are effectively uninterpreted.  Primitives produce
   -- constants (and constant-carrying objects).  Therefore, they cannot
   -- introduce locations.
   EOp _ _ es -> do
     ts <- mapM (typeCheck env) es
     return JS
   EIf _ e1 e2 e3 -> do
     t1 <- typeCheck env e1
     t2 <- typeCheck env e2
     t3 <- typeCheck env e3
     return (superType t2 t3)
   EObject _ props -> do
     ts <- mapM (typeCheck env) (map snd props)
     return Safe
   EGetField _ e1 e2 -> do
     t1 <- typeCheck env e1
     t2 <- typeCheck env e2
     case t2 of
       Safe -> return JS
       SafeString -> return JS
       otherwise -> fail $ "unsafe field lookup.\n" ++ 
                           "type of field is " ++ 
                           show (M.lookup "field" env) ++
                           "\n" ++
                           (pretty e2)
   EUpdateField _ e1 e2 e3 -> do
     t1 <- typeCheck env e1
     t2 <- typeCheck env e2
     t3 <- typeCheck env e3
     return JS
   ELabel _ lbl e -> typeCheck env e >> return JS
   EBreak _ lbl e -> typeCheck env e >> return JS
   EThrow _ e -> typeCheck env e
   ELet1{} -> error "unexpected ELet1 (removeHOAS not called?)"
   ELet2{} -> error "unexpected ELet2 (removeHOAS not called?)"
   EWhile _ e1 e2 -> do
     typeCheck env e1
     typeCheck env e2
     return JS
   ECatch _ e1 e2 -> do
     typeCheck env e1
     typeCheck env e2
     return JS
   EFinally _ e1 e2 -> do
     typeCheck env e1
     typeCheck env e2
     return JS
   EEval _ -> error "unexpected EEval"


isTypeable = typeCheck M.empty . removeHOAS
