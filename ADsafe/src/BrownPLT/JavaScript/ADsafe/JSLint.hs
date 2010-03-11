module BrownPLT.JavaScript.ADsafe.JSLint where

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State

import Data.Map ( Map )
import qualified Data.Map as M
import Data.Set ( Set )
import qualified Data.Set as S

import BrownPLT.JavaScript.Semantics.Syntax
import BrownPLT.JavaScript.Semantics.RemoveHOAS ( removeHOAS )

-- Types
--
data T = ADsafe | StringLit String | Global | Lint
  deriving ( Eq, Ord, Show )

-- Environment that maps identifiers to types.
--
type IdentEnv = Map Ident T

-- Typer Monad. Keeps track of identifier environment, and threading label
-- state.
--
newtype Typer a = Typer { runTyper :: ReaderT IdentEnv (Either String) a }
  deriving ( Functor, Monad, MonadReader IdentEnv )

varLookup :: Ident -> Typer (Maybe T)
varLookup = asks . M.lookup

-- Lookup a variable in the type environment.
varLookup' :: Ident -> Typer T
varLookup' x = do
  result <- varLookup x
  case result of
    Just t  -> return t
    Nothing -> fail $ "unbound identifier: " ++ x

checkViolation :: Expr SourcePos -> String -> Typer T
checkViolation e s = do
  typ <- typeCheck e
  case typ of 
    ADsafe    -> violation (label e) (s ++ " check violation")
    otherwise -> return typ

checkSubscript :: Expr SourcePos -> Typer T
checkSubscript e = do
  typ <- typeCheck e
  case typ of
    StringLit s ->
      if isSafeSubscript s
        then return typ
        else violation (label e) "subscript not safe"
    otherwise -> violation (label e) "subscript not string"

violation :: SourcePos -> String -> Typer T
violation p s = fail $ (show p) ++ " ADsafe violation " ++ s

isSafeSubscript :: String -> Bool
isSafeSubscript s =
  let hd = take 1 s in
    hd /= "_" && hd /= "-" && s `S.notMember` banned

-- What about: execScript?
--
banned :: Set String
banned = 
  S.fromList [ "arguments", "callee", "caller", "constructor", "eval"
             , "prototype", "unwatch", "valueOf", "watch" ]

typeCheck :: Expr SourcePos -> Typer T
typeCheck e = case e of
  ENumber _ _  -> return Lint
  EString _ s  -> return $ StringLit s
  EUndefined _ -> return Lint
  EBool _ _    -> return Lint
  ENull _      -> return Lint
  ELambda _ args b ->
    let env' = M.fromList [(arg, Lint) | arg <- args]
      in local (M.union env') $ typeCheck b
  EId _ id -> varLookup' id

  ELet _ binds body -> do
    boundTypes <- mapM typeCheck (map snd binds)
    let env' = M.fromList $ zip (map fst binds) boundTypes
    local (M.union env') $ typeCheck body

  EDeref _ e ->
    -- The result of (deref e) should have the same type as e
    typeCheck e

  EDeleteField _ e1 e2 -> do
    typ <- checkViolation e1 "delete-field object"
    checkSubscript e2
    return typ
  ESetRef a id e2  -> do
    typ <- varLookup' id
    case typ of
      ADsafe    -> violation (label e) "set-ref on ADSAFE" >> return ()
      otherwise -> return ()
    checkViolation e2 "set-ref expr"
    return typ
  ERef _ e -> typeCheck e
  EGetField _ e1 e2 -> do
    typ  <- typeCheck e1
    styp <- checkSubscript e2
    case (typ, styp) of
      (Global, StringLit s) ->
        if s == "ADSAFE"
          then return ADsafe
          else violation (label e) "not in the global scope" 
      (Global, _) -> violation (label e) "non-literal global lookup"
      _ -> return Lint
  ESeq _ e1 e2 -> do
    typeCheck e1
    typeCheck e2 
  EUpdateField _ e1 e2 e3 -> do
    typ <- checkViolation e1 "update-field object"
    checkSubscript e2
    checkViolation e3 "update-field expr"
    return typ

  EApp _ fe es -> do
    typeCheck fe
    mapM (flip checkViolation "app arg") es 
    return Lint
  EOp _ _ es -> do
    mapM typeCheck es
    return Lint

  EIf _ c e2 e3 -> do
    typeCheck c
    typeCheck e2
    typeCheck e3
  EObject _ props -> do
    mapM_ (flip checkViolation "object field") (map snd props)
    return Lint

  ELabel _ lbl e -> typeCheck e
  EBreak _ lbl e -> typeCheck e
  EWhile _ e1 e2 -> do
    typeCheck e1
    typeCheck e2
  EThrow _ e   -> checkViolation e "throw"
  ECatch _ _ _ -> violation (label e) "catch" 
  EFinally _ e1 e2 -> violation (label e) "finally"
  
  EEval _ -> error "unexpected EEval"
  ELet1{} -> error "unexpected ELet1 (removeHOAS not called?)"
  ELet2{} -> error "unexpected ELet2 (removeHOAS not called?)"

ljsEnv =
  [ "$Object.prototype", "$Function.prototype", "$Date.prototype"
  , "$Number.prototype", "$Array.prototype", "$Boolean.prototype"
  , "$Error.prototype", "$Boolean.prototype", "$Error.prototype" 
  , "$ConversionError.prototype", "$RangeError.prototype" 
  , "$ReferenceError.prototype", "$SyntaxError.prototype" 
  , "$TypeError.prototype", "$URIError.prototype"
  , "$RegExp.prototype" , "$String.prototype"
  ]

isTypeable e = (`runReaderT` initialEnv) $ runTyper $ checkViolation e "top-level"
  where
    initialEnv = M.fromList $
        [("$global", Global), ("$makeException", Lint)]
        ++ [(id, Lint) | id <- ljsEnv]
