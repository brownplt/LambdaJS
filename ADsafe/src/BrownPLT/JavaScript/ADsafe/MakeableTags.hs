module BrownPLT.JavaScript.ADsafe.MakeableTags ( isTypeable ) where

import BrownPLT.JavaScript.Semantics.ANF
import BrownPLT.JavaScript.Semantics.Syntax
import BrownPLT.JavaScript.Semantics.PrettyPrint

import Data.Generics

import qualified Data.Map as M
import qualified Data.Set as S

-- ASSUME -- makeableTagName the identifier ONLY set once
data Type = JS                    -- Could be anything
          | MTNObj                -- (deref makeableTagName)
          | MakeableOf Ident      -- (get-field [MTNOBJ] [x:AString])
          | IsMakeable Ident Bool -- ([MakeableOf x] !/=== true)
          | Makeable              -- true branch of IsMakeable test
          | Typeof Ident          -- (typeof x)
          | IsString Ident Bool   -- ([Typeof x] !/=== "string")
          | AString               -- we know it's a string (not the value though)
          | CString String        -- constant strings
          | NotDocument           -- definitely not the document object, or a field of it
            deriving (Show, Eq, Ord)

type Env = M.Map Ident Type                     

subType :: Type -> Type -> Bool
subType a b | a==b = True
subType a NotDocument = a /= JS
subType _ JS = True
subType _ _ = False

safe :: Type -> Bool
safe t | subType t Makeable = True
safe (CString s) = True -- if s is a safe string
safe _ = False

superType :: Type -> Type -> Type
superType a b | (a==b) = a
superType a b | (subType a b) = b
superType a b | (subType b a) = a
superType a b | (subType a NotDocument) && (subType b NotDocument) = NotDocument
superType _ _ = JS

typeVal :: (Show a, Data a) => Env -> Value a -> Either String Type
typeVal env v = 
    case v of
      VString _ s -> return (CString s)
      VNumber _ d -> return NotDocument
      VUndefined _ -> return NotDocument
      VNull _ -> return NotDocument
      VEval _ -> return NotDocument
      VBool _ b -> return NotDocument
      VId a "makeableTagName" -> return MTNObj
      VId a "document" -> return JS
      VId a "$global" -> return JS
      VId a x -> case M.lookup x env of
                  Just t -> return t
                  Nothing -> fail ("unbound id" ++ (show x) ++ (show a))
      VLambda _ ids body -> do
             let env' = (M.fromList [(x, NotDocument) | x <- ids])
             etype <- typeExp (M.union env' env) body
             return etype
                      
typeBind :: (Show a, Data a) => Env -> BindExp a -> Either String Type
typeBind env b = 
    case b of
      BSetRef a loc val -> do
             vtype <- typeVal env val
             return vtype
      BRef a val -> do
             typeVal env val
      BDeref a val -> do
             typeVal env val
      BUpdateField a o f v -> do
             otype <- typeVal env o
             typeVal env f
             typeVal env v
             return otype
      BGetField a (VId a2 x) (VString a3 "document") -> do
             xtype <- typeVal env (VId a2 x)
             return JS
      BGetField a1 obj (VId a2 x) -> do
             otype <- typeVal env obj
             ftype <- typeVal env (VId a2 x)
             case (otype, ftype) of
               (MTNObj, AString) -> return (MakeableOf x) -- should only have strings here, for the test to be valid
               (MTNObj, _) -> fail ("useless or deceptive reference of MTN" ++ show b ++ show otype ++ show ftype)
               (JS, CString s) | s /= "document" && s /= "createElement" && s /= "$code" -> return NotDocument
               (a, _) -> return a
      BGetField a obj field -> do
             otype <- typeVal env obj
             ftype <- typeVal env field
             case (otype, ftype) of
               (MTNObj, _) -> fail ("useless or deceptive reference of MTN" ++ show b ++ show otype ++ show ftype)
               (JS, CString s) | s /= "document" && s /= "createElement" && s /= "$code" -> return NotDocument
               (a, _) -> return a
      BDeleteField a obj field -> do
             otype <- typeVal env obj
             ftype <- typeVal env field
             return NotDocument
      BObject a [("length", (VNumber al 1.0)),
                 ("callee", cid),
                 ("$class", (VString acl "Object")),
                 ("$proto", (VId ap "$Object.prototype")),
                 ("$isArgs", (VBool ag True)),
                 ("0", x)] -> do
             xtype <- typeVal env x
             case xtype of
               AString ->  return AString
               Makeable -> return Makeable
               otherwise -> return xtype
      BObject a fields -> do
        otypes <- mapM (\(name,val) -> typeVal env val) fields
        if not (all (\t -> subType t NotDocument) otypes) then
            return JS else
            return NotDocument
      BApp a f args -> do
        ftype <- typeVal env f
        atypes <- mapM (typeVal env) args
        let atypes' = if atypes == [] then [] else tail atypes -- ignore the 1st arg (assume unsafe, it's this)
        case ftype of
          JS -> if not (all safe atypes') then
                    fail ("Unsafe application: " ++ show b ++ show ftype ++ show atypes') else
                    return NotDocument
          otherwise -> return NotDocument
      BOp a OTypeof [(VId a2 x)] -> do
        xtype <- typeVal env (VId a2 x)
        return (Typeof x)
      BOp a OStrictEq [(VId a2 x), (VString a3 "string")] -> do
        xtype <- typeVal env (VId a2 x)
        case xtype of
          Typeof y -> return (IsString y True)
          otherwise -> return NotDocument
      BOp a OStrictEq [v, (VBool a2 True)] -> do
        vtype <- typeVal env v
        case vtype of
          MakeableOf x -> return (IsMakeable x True)
          otherwise -> return NotDocument
      BOp a OPrimToStr [v] -> do
        vtype <- typeVal env v
        return AString
      BOp a op args -> do
             atypes <- mapM (typeVal env) args
             return NotDocument
      BIf a c (AReturn _ (VBool _ False)) (AReturn _ (VBool _ True)) -> do
             ctype <- typeVal env c
             case ctype of
               IsMakeable x b -> return (IsMakeable x (not b))
               IsString x b -> return (IsString x (not b))
               otherwise -> return NotDocument
      BIf a c t e -> do
             ctype <- typeVal env c
             let tenv = case ctype of
                          IsString x True -> M.insert x AString env
                          IsMakeable x True -> M.insert x Makeable env
                          otherwise -> env 
                 eenv = case ctype of 
                          IsString x False -> M.insert x AString env
                          IsMakeable x False -> M.insert x Makeable env
                          otherwise -> env
             ttype <- typeExp tenv t
             etype <- typeExp eenv e
             return (superType ttype etype)
      BValue a v -> do
             typeVal env v


typeExp :: (Show a, Data a) => Env -> Exp a -> Either String Type
typeExp env e = 
    case e of
      ALet a binds body -> do
             btypes <- mapM (typeBind env) (map snd binds)
             let env' = M.fromList (zip (map fst binds) btypes)
             btype <- typeExp (M.union env' env) body
             return btype
      ASeq a e1 e2 -> do
             e1type <- typeExp env e1
             e2type <- typeExp env e2
             return e2type
      ALabel a lbl body -> do
             btype <- typeExp env body
             return btype
      ABreak a lbl v -> do
             vtype <- typeVal env v
             return vtype
      AThrow a v -> do
             vtype <- typeVal env v
             return vtype
      ACatch a body catch -> do
             btype <- typeExp env body
             ctype <- typeVal env catch
             return btype
      AFinally a body rest -> do
             btype <- typeExp env body
             rtype <- typeExp env rest
             return (superType btype rtype)
      AReturn a v -> typeVal env v
      ABind a b -> typeBind env b

allEnv = 
  [ "$Object.prototype", "$Function.prototype", "$Date.prototype"
  , "$Number.prototype", "$Array.prototype", "$Boolean.prototype"
  , "$Error.prototype", "$Boolean.prototype", "$Error.prototype" 
  , "$ConversionError.prototype", "$RangeError.prototype" 
  , "$ReferenceError.prototype", "$SyntaxError.prototype" 
  , "$TypeError.prototype", "$URIError.prototype", "Object", "Function"
  , "Array", "$RegExp.prototype", "RegExp", "Date", "Number"
  , "$String.prototype", "String", "Boolean", "Error", "ConversionError"
  , "EvalError", "RangeError", "ReferenceError", "SyntaxError", "TypeError"
  , "URIError", "$makeException"
  ]

globalEnv = allEnv -- change to [] if using ECMA environment

isTypeable :: (Data a, Show a) => Exp a -> Either String Type
isTypeable = typeExp startEnv
    where startEnv = (M.fromList (map (\x -> (x, NotDocument)) globalEnv))


