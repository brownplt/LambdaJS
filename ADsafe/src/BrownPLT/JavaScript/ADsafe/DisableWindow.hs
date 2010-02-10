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

data RType = RWindow
           | RSafe
             deriving (Show, Ord, Eq)

data AType = ASafe
           | AVar RType -- a variable type is either RWindow or RSafe
           | AString String
           | AWindowOf Ident
           | ATypeIs Ident RType
           | ATypeIsNot Ident RType
           | ATypeAnd AType
           | ATypeOr AType
             deriving (Show, Ord, Eq)

type TEnv = M.Map Ident AType

-- returns the new value and the type for it
typeVal :: (Show a, Data a) => TEnv -> Value a -> Either String AType
typeVal env v =
    case v of
      VId a "$global" -> return (AVar RWindow) -- not safe
      VString a s -> return (AString s)
      VId a x -> case M.lookup x env of
                   Just t -> return t
                   Nothing -> fail "unbound id"
      VLambda a ids body -> do
          let env' = (M.fromList (map (\x -> if x == "this" then (x, AVar RWindow) else (x, ASafe)) ids))
          typeExp (M.union env' env) body
          return ASafe
      VNumber a n -> return ASafe
      VBool a n -> return ASafe
      VUndefined a -> return ASafe
      VNull a -> return ASafe
      VEval a -> return ASafe


typeBind :: (Data a, Show a) => TEnv -> BindExp a -> Either String AType 
typeBind env b =
    case b of 
      BSetRef a loc val -> do
             vtype <- typeVal env val
             case vtype of 
               (AVar RWindow) -> fail ("Can't store window in a ref: " ++ (show (label b)))
               otherwise -> return vtype
      BRef a val -> do
             typeVal env val
      BDeref a val -> do
             typeVal env val
      BGetField a (VId _ x) (VString _ "window") -> do 
--             fail "found a window"
             return (AWindowOf x) -- ANF ftw
      BGetField a obj field -> do
             return ASafe -- we won't ever *store* window, so safe
      BUpdateField a obj field val -> do
             vtype <- typeVal env val
             case vtype of
               (AVar RWindow) -> fail ("Can't store window in an object")
               otherwise -> return vtype
      BDeleteField a obj field -> do
             return ASafe
      BObject a fields -> do
             otypes <- mapM (typeVal env) (map snd fields)
             if S.member (AVar RWindow) (S.fromList otypes) then
                 return (AVar RWindow) else
                 return ASafe
      BOp a OStrictEq [(VId _ "this"), y] -> do
             ytype <- typeVal env y
             case ytype of
               AWindowOf x -> return (ATypeIs x RWindow)
               otherwise -> return ASafe
      BOp a OPrimToBool [x] -> do
             tx <- typeVal env x
             let rettype = case tx of
                             ATypeIs x r -> ATypeIs x r
                             ATypeIsNot x r -> ATypeIsNot x r
                             ATypeOr t -> ATypeOr t
                             ATypeAnd t -> ATypeAnd t
                             otherwise -> ASafe
             return rettype
      BOp a op args -> do
             otypes <- mapM (typeVal env) args
             return ASafe
      BApp a f args -> do
             ftype <- typeVal env f
             atypes <- mapM (typeVal env) args
             let atypes' = if atypes == [] then [] else tail atypes -- ignore the 1st arg (assume unsafe)
             if S.member (AVar RWindow) (S.fromList atypes') then
                 fail ("Can't pass Window as a function argument." ++ (show b)) else
                 return ASafe
      -- desugared 'not' operator
      BIf a c (AReturn _ (VBool _ False)) (AReturn _ (VBool _ True)) -> do
             tc <- typeVal env c
             case tc of
               (ATypeIs x RWindow) -> return (ATypeIsNot x RWindow)
               (ATypeIsNot x RWindow) -> return (ATypeIs x RWindow)
               otherwise -> return ASafe
      BIf a c t e -> do
             ctype <- typeVal env c
             ttype <- 
                 case ctype of 
                   (ATypeAnd (ATypeIsNot x RWindow)) -> typeExp (M.insert x (AVar RSafe) (M.insert "this" (AVar RSafe) env)) e
                   (ATypeIsNot x RWindow) -> 
                       typeExp (M.insert "this" (AVar RSafe) env) t
                   otherwise -> typeExp env t
             etype <- 
                 case ctype of 
                   (ATypeOr (ATypeIs x RWindow)) -> typeExp (M.insert x (AVar RSafe) (M.insert "this" (AVar RSafe) env)) e
--                   (ATypeIs x RWindow) -> fail ("match typecheck" ++ (show a))
                   (ATypeIs x RWindow) -> typeExp (M.insert x (AVar RSafe) (M.insert "this" (AVar RSafe) env)) e
                   otherwise -> typeExp env e
             case (ctype, ttype, etype) of
               (ATypeOr (ATypeIs x1 RWindow), ATypeOr (ATypeIs x2 RWindow), _) | x1 == x2 -> return (ATypeOr (ATypeIs x2 RWindow))
--               ((ATypeIs x1 RWindow), (ATypeIsNot x2 RWindow), _) | x1 == x2 -> return (ATypeAnd (ATypeIs x2 RWindow))
               ((ATypeIs x1 RWindow), (ATypeIs x2 RWindow), _) | x1 == x2 -> return (ATypeOr (ATypeIs x2 RWindow))
               ((ATypeIs x1 RWindow), (ATypeIsNot x2 RWindow), _) | x1 == x2 -> return (ATypeAnd (ATypeIs x2 RWindow))
               ((ATypeIsNot x1 RWindow), (ATypeIsNot x2 RWindow), _) | x1 == x2 -> return (ATypeOr (ATypeIs x2 RWindow))
               ((ATypeIsNot x1 RWindow), (ATypeIs x2 RWindow), _) | x1 == x2 -> return (ATypeAnd (ATypeIs x2 RWindow))
               otherwise ->
                   if S.member (AVar RWindow) (S.fromList [ttype,etype]) then
                       return (AVar RWindow) else
                       return ASafe
      BValue a v -> do
             typeVal env v

typeExp :: (Show a, Data a) => TEnv -> Exp a -> Either String AType
typeExp env e =
    case e of
      ALet a binds body -> do
             btypes <- mapM (typeBind env) (map snd binds)
             let env' = M.fromList (zip (map fst binds) btypes)
             btype <- typeExp (M.union env' env) body
             return btype
      ARec a binds body -> do
             btypes <- 
                 mapM (\pair -> 
                           (typeVal (M.insert (fst pair) ASafe env) (snd pair))) 
                 binds
             let env' = M.fromList (zip (map fst binds) btypes)
             btype <- typeExp (M.union env' env) body
             return btype
      ALabel a lbl body -> do
             btype <- typeExp env body
             return btype
      ABreak a lbl v -> do
             vtype <- typeVal env v
             case vtype of
               (AVar RWindow) -> fail ("Can't break on Window" ++ show e)
               otherwise -> return vtype
      AThrow a v -> do
             vtype <- typeVal env v
             case vtype of
               (AVar RWindow) -> fail "Can't throw Window"
               otherwise -> return vtype
      ACatch a body catch -> do
             btype <- typeExp env body
             ctype <- typeVal env catch
             return ASafe
      AFinally a body final -> do
             btype <- typeExp env body
             ftype <- typeExp env final
             return ASafe
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


isTypeable = typeExp M.empty . addGlobals
    where addGlobals b = ALet nopos [(x, (BValue nopos (VUndefined nopos))) | x <- globalEnv] b
