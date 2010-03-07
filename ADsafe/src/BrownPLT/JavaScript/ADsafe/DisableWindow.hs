module BrownPLT.JavaScript.ADsafe.DisableWindow ( isTypeable ) where


import BrownPLT.JavaScript.Semantics.ANF
import BrownPLT.JavaScript.Semantics.Syntax
import BrownPLT.JavaScript.Semantics.PrettyPrint

import Data.Generics

import qualified Data.Map as M
import qualified Data.Set as S


{-
Typechecks adsafe for expressions that allow 'a window expression' to 'escape.'

'A window expression' (types to Window) starts as one of:

(deref $global)
this

And the type propagates through derefing and setting fields of objects.
The "this" identifier can type to Safe instead of Window if it passes
through a check of the form 

if (this === this.window) ...

'Escaping' is defined as:

Being returned,
Being passed as an argument that isn't the first in the list,
Being put into an object with update-field,
Being stored in a reference.

This is really an application of occurrence typing.  There are extra,
more complicated rules for dealing with checks like

if (this === this.window || ...)

or 

if (this !== this.window)

It could be that these are needlessly complicated, and implementing
occurrence more generally would accommodate these changes.  I'm not sure
what proof of soundness for this type system looks like right now, so
that's the next step.  Writing down this type system results in no less
than 12 different judgements for IF, so there's room for improvement
here.
-}


data Type = Window
          | Safe
          | JS
          | This
          | IsWin Ident Bool
          | MaybeWin Ident Bool
          | WindowOf Ident
          | AString String
            deriving (Show, Ord, Eq)

type Env = M.Map Ident Type

-- Note that MaybeWin <: JS, not Safe -- we don't think about what
-- the "other" branch is, so assume it could be dangerous
subType :: Type -> Type -> Bool
subType a b | (a==b) = True
subType _ JS = True -- The top type
subType (WindowOf x) Window = True -- WindowOf is dangerous
subType This Window = True      -- As is the unchecked this type
subType (AString s) Safe = True -- Constant strings are not dangerous
subType (IsWin x b) Safe = True -- IsWin is a boolean, not dangerous
subType _ _ = False

superType :: Type -> Type -> Type
superType a b | (a==b) = a
superType a b | (subType a b) = b
superType a b | (subType b a) = a
superType _ _ = JS

-- returns the new value and the type for it
typeVal :: (Show a, Data a) => Env -> Value a -> Either String Type
typeVal env v =
    case v of
      VId a "$global" -> return Window
      VString a s -> return (AString s)
      VId a x -> case M.lookup x env of
                   Just t -> return t
                   Nothing -> fail ("unbound id" ++ ((show x) ++ (show a)))
      -- Assume all arguments other than "this" are safe.  Assume "this" is dangerous
      VLambda a ids body -> do
          let env' = (M.fromList (map (\x -> if x == "this" then 
                                                 (x, This) else -- initially type "This"
                                                 (x, Safe)) 
                                  ids))
          etype <- typeExp (M.union env' env) body
          return Safe
      VNumber a n -> return Safe
      VBool a n -> return Safe
      VUndefined a -> return Safe
      VNull a -> return Safe
      VEval a -> return Safe


typeBind :: (Data a, Show a) => Env -> BindExp a -> Either String Type 
typeBind env b =
    case b of 
      BSetRef a loc val -> do
             vtype <- typeVal env val
             if subType vtype Safe then
                 return vtype else
                 fail ("Can't store window in a ref: " ++ (show b))
      BRef a val -> do
             typeVal env val
      BDeref a val -> do
             typeVal env val
      BGetField a (VId a2 x) s -> do
             xtype <- typeVal env (VId a2 x)
             stype <- typeVal env s
             case stype of
               AString "window" ->                        
                   if subType xtype This then
                       return (WindowOf "this")  else
                       if subType xtype Safe then
                           return Safe else
                           return JS 
               AString _ -> return Safe
               otherwise ->              
                   if subType xtype Safe then
                       return Safe else
                       return JS
      BGetField a obj field -> do
             ftype <- typeVal env field
             otype <- typeVal env obj
             if subType otype Safe then -- Only Safe if it came from Safe
                 return Safe else
                 return JS
      BUpdateField a obj field val -> do
             vtype <- typeVal env val
             if not (subType vtype Safe) then
                 fail ("Can only store Safe values in objects" ++ (show b)) else
                 return vtype
      BDeleteField a obj field -> do
             return Safe
      BObject a fields -> do
             otypes <- mapM (typeVal env) (map snd fields)
             if not (all (\t -> subType t Safe) otypes) then
                 return JS else
                 return Safe
      BOp a OStrictEq [(VId _ "this"), y] -> do
             ytype <- typeVal env y
             case ytype of
               WindowOf x -> return (IsWin x True)
               otherwise -> return Safe
      BOp a OPrimToBool [x] -> do
             tx <- typeVal env x
             case tx of
               IsWin x b -> return $ IsWin x b
               MaybeWin x b -> return $ MaybeWin x b
               otherwise -> return Safe
      BOp a op args -> do
             otypes <- mapM (typeVal env) args
             return Safe
      BApp a f args -> do
             ftype <- typeVal env f
             atypes <- mapM (typeVal env) args
             let atypes' = if atypes == [] then [] else tail atypes -- ignore the 1st arg (assume unsafe)
             if all (\t -> subType t Safe) atypes' then
                 return Safe else
                 fail ("All arguments must be Safe." ++ (show b) ++ (show atypes'))
      -- desugared 'not' operator
      BIf a c (AReturn _ (VBool _ False)) (AReturn _ (VBool _ True)) -> do
             tc <- typeVal env c
             case tc of
               IsWin x b -> return (IsWin x (not b))
               otherwise -> return Safe
      BIf a c t e -> do
             ctype <- typeVal env c
             ttype <- 
                 case ctype of 
                   (MaybeWin x False) -> typeExp (M.insert x Safe env) t
                   (IsWin x False) -> typeExp (M.insert x Safe env) t
                   otherwise -> typeExp env t
             etype <- 
                 case ctype of 
                   (MaybeWin x True) -> typeExp (M.insert x Safe env) e
                   (IsWin x True) -> typeExp (M.insert x Safe env) e
                   otherwise -> typeExp env e
             case (ctype, ttype) of
               -- We only need these three
               (MaybeWin x1 True, MaybeWin x2 True) | (x1==x2) -> return (MaybeWin x1 True)
               (IsWin x1 True, IsWin x2 True) | (x1==x2) -> return (MaybeWin x1 True)
               (IsWin x1 True, IsWin x2 False) | (x1==x2) -> return (MaybeWin x1 False)
               otherwise -> return (superType ttype etype)
      BValue a v -> 
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
             if not (subType vtype Safe) then
                 fail ("Must break on Safe" ++ show e ++ show vtype) else
                 return vtype
      AThrow a v -> do
             vtype <- typeVal env v
             if not (subType vtype Safe) then
                 fail ("Must throw Safe" ++  (show e) ++ (show vtype)) else
                 return vtype
      ACatch a body catch -> do
             btype <- typeExp env body
             ctype <- typeVal env catch
             return (superType btype ctype)
      AFinally a body final -> do
             btype <- typeExp env body
             ftype <- typeExp env final
             return (superType btype ftype)
      AReturn a v -> do
             typeVal env v
      ABind a b -> do
             typeBind env b

safeEnv = 
  [ "$Object.prototype", "$Function.prototype", "$Date.prototype"
  , "$Number.prototype", "$Array.prototype", "$Boolean.prototype"
  , "$Error.prototype", "$Boolean.prototype", "$Error.prototype" 
  , "$ConversionError.prototype", "$RangeError.prototype" 
  , "$ReferenceError.prototype", "$SyntaxError.prototype" 
  , "$TypeError.prototype", "$URIError.prototype", "Object", "Function"
  , "$RegExp.prototype", "RegExp", "Date", "Number"
  , "$String.prototype", "String", "Boolean", "Error", "ConversionError"
  , "EvalError", "RangeError", "ReferenceError", "SyntaxError", "TypeError"
  , "URIError", "$makeException"
  ]

windowEnv = 
    [ "$global", "Array", "$Array.prototype" ]

isTypeable :: (Data a, Show a) => Exp a -> Either String Type
isTypeable = typeExp startEnv
    where startEnv = (M.union (M.fromList (map (\x -> (x, Window)) windowEnv))
                           (M.fromList (map (\x -> (x, Safe)) safeEnv)))