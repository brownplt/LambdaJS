module BrownPLT.JavaScript.ADsafe.DisableEval ( isEvalTypeable ) where

import qualified Data.Map as M

import BrownPLT.JavaScript.Semantics.ANF
import BrownPLT.JavaScript.Semantics.Syntax

import BrownPLT.JavaScript.Semantics.PrettyPrint

type Env = M.Map Ident T

data T = JS | Eval deriving (Show, Eq, Ord)

subType :: T -> T -> Bool
subType Eval JS = False
subType _ _ = True

superType :: T -> T -> T
superType a b | a==b = a
superType _ _ = Eval

typeVal :: Env -> Value a -> Either String T
typeVal env v = 
    case v of 
      VNumber a n -> return JS
      VString a s -> return JS
      VBool a b -> return JS
      VUndefined a -> return JS
      VNull a -> return JS
      VId a x -> case M.lookup x env of
                   Just t -> return t
                   Nothing -> error ("unbound id: " ++ x)
      VLambda a args body -> do
             let env' = M.fromList (map (\x -> (x,Eval)) args)
             typeExp (M.union env' env) body
             return JS
      VEval a -> return Eval

typeBind :: Env -> BindExp a -> Either String T
typeBind env b = 
    case b of 
      BObject a fields -> do 
             ts <- mapM (typeVal env) (map snd fields)
             let t = foldr superType JS ts
             return t
      BSetRef a v1 v2 -> do
             typeVal env v1
             typeVal env v2
             return JS
      BRef a v -> do
             typeVal env v
      BDeref a v -> do
             val <- typeVal env v
             return val
      BGetField _ v1 (VString _ "eval") -> return Eval
      BGetField _ v1 (VId _ "eval") -> return Eval
      BGetField _ v1 (VString _ "$code") -> do
             typeVal env v1
      BGetField _ v1 v2 -> do
             typeVal env v1
             typeVal env v2
             return JS
      BUpdateField a v1 v2 v3 -> do
             typeVal env v1
             typeVal env v2
             typeVal env v3
             return JS
      BDeleteField a v1 v2 -> do
             typeVal env v1
             typeVal env v2
      BValue a v -> do
             typeVal env v
      BOp a o vals -> do
             mapM (typeVal env) vals
             return JS
      BApp a func args -> do
             ftype <- typeVal env func
             case ftype of
               JS -> do 
                 ts <- mapM (typeVal env) args
                 if all (\t -> subType t JS) ts then
                     return JS else
                     fail ("fail -- arguments" ++ (prettyANF (ABind a (BApp a func args))))
               otherwise -> fail "fail -- bad app"
      BIf a v e1 e2 -> do
          typeVal env v
          typeExp env e1
          typeExp env e2
          return JS

typeExp :: Env -> Exp a -> Either String T
typeExp env e =
    case e of 
      ALet _ [(id1, (BSetRef _ (VId a id2) val))] body -> do
             idtype <- typeVal env val
             typeExp (M.insert id1 idtype (M.insert id2 idtype env)) body
      ALet a binds body -> do
             btypes <- mapM (typeBind env) (map snd binds)
             let env' = M.fromList (zip (map fst binds) btypes)
             typeExp (M.union env' env) body
      ARec a binds body -> do
             btypes <- mapM (typeVal env) (map snd binds)
             let env' = M.fromList (zip (map fst binds) btypes)
             typeExp (M.union env' env) body
      ALabel a lbl e -> do
             typeExp env e
      ABreak a "$return" v -> do
             t <- typeVal env v
             case t of 
               JS -> return JS
               otherwise -> fail "Bad return"
      ABreak _ lbl v -> do
             typeVal env v
             return JS
      AThrow a v -> do
             typeVal env v
      ACatch a e v -> do
             typeExp env e
             typeVal env v
      AFinally a e1 e2 -> do
             typeExp env e1
             typeExp env e2
      AReturn a v -> do
             typeVal env v
      ABind a b -> do
             typeBind env b



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

isEvalTypeable = typeExp M.empty . addGlobals
    where addGlobals b = ALet nopos [(x, (BValue nopos (VUndefined nopos))) | x <- globalEnv] b