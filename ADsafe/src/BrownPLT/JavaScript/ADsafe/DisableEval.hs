module BrownPLT.JavaScript.ADsafe.DisableEval ( isTypeable ) where

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State

import Data.Map ( Map )
import qualified Data.Map as M
import Data.Set ( Set )
import qualified Data.Set as S

import BrownPLT.JavaScript.Semantics.Syntax
import BrownPLT.JavaScript.Semantics.RemoveHOAS ( removeHOAS )
import BrownPLT.JavaScript.Semantics.PrettyPrint ( pretty )

import Text.ParserCombinators.Parsec.Pos ( sourceLine, sourceColumn )

-- Types
--
-- Note that
-- 
--   Obj [] <: Safe     and     Safe <: Obj []
--
-- so they're the same type.
--
data T = Safe | JS | Ref T | Obj [Ident]
  deriving ( Show, Eq, Ord )

-- Environment that maps identifiers to types.
--
type IdentEnv = Map Ident T

-- Environment that maps identifiers to types.
-- 
type LabelEnv = Map Label T

-- Typer Monad. Keeps track of identifier environment, and threading label
-- state.
--
newtype Typer a = Typer (StateT LabelEnv (ReaderT IdentEnv (Either String)) a)
  deriving ( Functor, Monad, MonadState LabelEnv, MonadReader IdentEnv, MonadError String )

subType :: T -> T -> Bool
subType x y | x == y = True

subType (Ref x)  (Ref y) = subType x y
subType (Ref x)  y       = subType x y
subType x        (Ref y) = subType x y

subType (Obj []) y        = subType Safe y
subType y        (Obj []) = subType y    Safe
subType (Obj xs) (Obj ys) = (S.fromList xs)
                                        `S.isSubsetOf` (S.fromList ys)
subType Safe     (Obj ys) = False

subType JS _    = False
subType _  JS   = True
subType _  Safe = True

isSafe :: T -> Bool
isSafe Safe     = True
isSafe (Obj []) = True
isSafe _        = False

superType :: T -> T -> T
superType t1 t2 
    | subType t1 t2 = t2
    | subType t2 t1 = t1
    | otherwise     = error "omg incomparable"

varLookup :: Ident -> Typer (Maybe T)
varLookup = asks . M.lookup

-- Lookup a variable in the type environment.
varLookup' :: Ident -> Typer T
varLookup' x 
    | x == "Function" = return JS
    | x `elem` globalEnv = return $
        Obj ["eval", "constructor", "$proto", "prototype"]
    | otherwise = do
        result <- varLookup x
        case result of
            Just t  -> return t
            Nothing -> throwError $ "unbound identifier: " ++ x

typeCheck :: Expr SourcePos -> Typer T
typeCheck e = case e of
  ENumber _ _  -> return Safe
  EString _ _  -> return Safe
  EUndefined _ -> return Safe
  EBool _ _    -> return Safe
  ENull _      -> return Safe
  ELambda a xs e ->
    let env' = M.fromList [(x, Safe) | x <- xs]
      in local (M.union env') $ typeCheck e
  EId _ x -> varLookup' x
  ELet _ binds body -> do
    boundTypes <- mapM typeCheck (map snd binds)
    let env' = M.fromList $ zip (map fst binds) boundTypes
    local (M.union env') $ typeCheck body
  EDeref _ e -> do
    -- The result of (deref e) should have the same type as e
    t <- typeCheck e
    case t of
        Ref tr    -> return tr
        otherwise -> return t
  EDeleteField _ e1 e2 -> do
    t1 <- typeCheck e1
    t2 <- typeCheck e2
    return t1
  ESetRef a id e2 -> do
    t1 <- varLookup' id
    t2 <- typeCheck e2
    when (not $ subType t2 t1)
        (throwError $ "bad assignment of " ++ (show id) ++ " to\n\n" ++ (pretty e2) ++ "\nat " ++ (show a) ++ "\n" ++ (show t2) ++ " !<: " ++ (show t1))
    return t1
  ERef _ e -> do
    -- The result of (ref e) should have the same type as e
    t <- typeCheck e
    return $ Ref t
  EApp _ fe es -> do
    t  <- typeCheck fe
    ts <- mapM typeCheck es
    case subType t Safe of
      True  -> case all (\t -> subType t Safe) ts of
                True  -> return Safe
                False -> throwError "unsafe application (arguments)"
      False -> throwError "unsafe application"
  ESeq _ e1 e2 -> do
    t1 <- typeCheck e1
    t2 <- typeCheck e2
    return t2
  EOp _ _ es -> do
    ts <- mapM typeCheck es
    return Safe
  EIf _ c e2 e3 -> do
    t1 <- typeCheck c
    t2 <- typeCheck e2
    t3 <- typeCheck e3
    return $ superType t2 t3
  EObject _ props -> do
    ts <- mapM (\(n, e) -> do { t <- typeCheck e; return (n, t) }) props
    return $ Obj [n | (n, t) <- ts, not (subType t Safe)]
  EGetField _ e1 e2 -> do
    tobj <- typeCheck e1
    tfld <- typeCheck e2
    case tobj of
      Obj ids ->
        case e2 of
          (EString _ id) -> if id `elem` ids
                              then return JS
                              else return Safe
          _              -> return JS
      -- Handle Safe, Ref T, and JS
      otherwise -> if subType tobj Safe
                     then return Safe
                     else return JS
  EUpdateField _ e1 e2 e3 -> do
    tobj <- typeCheck e1
    tfld <- typeCheck e2
    trhs <- typeCheck e3
    case tobj of
      Obj ids -> 
        case e2 of
          (EString _ id) -> if id `elem` ids
                              then return tobj
                              else if isSafe trhs then return tobj else return $ Obj (id:ids)
          _              -> if isSafe trhs then return tobj else return JS
      otherwise -> if subType tobj Safe
                     then if subType trhs tobj then return tobj else return trhs
                     else return JS
  ELabel _ lbl e -> do
    te  <- typeCheck e
    labs <- get
    let mtl = M.lookup lbl labs
    case mtl of
        Just tl -> do
          put $ M.delete lbl labs
          return $ superType te tl
        Nothing -> return te
  EBreak _ lbl e -> do
    te <- typeCheck e
    labs <- get
    let mtl = M.lookup lbl labs
    case mtl of
        Just tl -> do
          put $ M.insert lbl (superType tl te) labs
          return te
        Nothing -> do
          put $ M.insert lbl te labs
          return te
  EThrow _ e -> typeCheck e >> return Safe
  EWhile _ e1 e2 -> do
    t1 <- typeCheck e1
    t2 <- typeCheck e2
    return Safe
  ECatch _ e1 e2 -> do
    t1 <- typeCheck e1
    t2 <- typeCheck e2
    return Safe
  EFinally _ e1 e2 -> do
    t1 <- typeCheck e1
    t2 <- typeCheck e2
    return Safe
  EEval _ -> return JS
  ELet1{} -> error "unexpected ELet1 (removeHOAS not called?)"
  ELet2{} -> error "unexpected ELet2 (removeHOAS not called?)"


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
  , "uRIError", "this", "$makeException", "decodeURI"
  ]

isTypeable = runTyper . typeCheck . addGlobals . removeHOAS
  where addGlobals b = ELet nopos [(x, EUndefined nopos) | x <- globalEnv] b
        runTyper (Typer m) = runReaderT (evalStateT m M.empty) M.empty

