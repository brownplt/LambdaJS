module BrownPLT.JavaScript.ADsafe.DisableBanned ( isTypeable ) where

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
data T = SafeString | Safe | World | JS
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
subType _ JS         = True
subType SafeString _ = True
subType Safe       World  = True
subType _          _ = False

superType :: T -> T -> T
superType t1 t2 =
  case t1 `compare` t2 of
    LT -> t2
    GT -> t1
    EQ -> t1


-- ADsafe banned list

-- By putting $proto in this list, I'm making the following assumption:

-- No object's "prototype" property has a built-in property we don't
-- want to leak to the clients, except for those named in the banned
-- list.  Clearly, if window gets set as your $proto, we have
-- problems, but that is what the window checker is for
banned :: Set String
banned = 
  S.fromList [ "arguments", "callee", "caller", "constructor", "eval"
             , "prototype", "unwatch", "valueOf", "watch", "$proto" ]

isBanned :: String -> Bool
isBanned s | S.member s banned = True
isBanned _ = False

typeCheck :: Expr SourcePos -> Typer T
typeCheck e = case e of
  ENumber _ _  -> return Safe
  EString _ s  -> return $ if isBanned s then JS else Safe
  EUndefined _ -> return Safe
  EBool _ _    -> return Safe
  ENull _ -> return Safe
  ELambda a xs e ->
      let env' = M.fromList (map (\x -> if x == "this" then (x, JS) else (x, JS)) xs)
      in local (M.union env') $ typeCheck e
  EId _ x -> do
    result <- asks $ M.lookup x
    case result of
      Just t  -> return t
      Nothing -> error $ "unbound identifier: " ++ x
  ELet _ binds body -> do
    boundTypes <- mapM typeCheck (map snd binds)
    let env' = M.fromList $ zip (map fst binds) boundTypes
    local (M.union env') $ typeCheck body
  EDeref _ e -> do
    -- The result of (deref e) should have the same type as e
    typeCheck e
  EDeleteField _ e1 e2 -> do
    typeCheck e1
    typeCheck e2
    return JS
  ESetRef _ e1 e2 -> do
    --typeCheck e1
    typeCheck e2
    return JS
  ERef _ e -> do
    -- The result of (ref e) should have the same type as e
    typeCheck e
  EApp _ e es -> do
    t  <- typeCheck e
    ts <- mapM typeCheck es
    case subType t World of
      True  -> return t
      False -> return JS
  ESeq _ e1 e2 -> do
    t1 <- typeCheck e1
    typeCheck e2
  EOp _ OPrimToStr [e] -> do
    typeCheck e
  -- Other primitives are effectively uninterpreted.  Primitives produce
  -- constants (and constant-carrying objects).  Therefore, they cannot
  -- introduce locations.
  EOp _ _ es -> do
    ts <- mapM typeCheck es
    return World
  EIf _ c@(EOp _ OStrictEq [EOp _ OTypeof [EId _ x], EString _ "location"]) e2 e3 -> do
    result <- asks $ M.lookup x
    case result of
       Just SafeString -> typeCheck e3
       otherwise       -> checkIf c e2 e3
  EIf _ c@(EOp _ OStrictEq [EOp _ OTypeof [EId _ x], EString _ "string"]) e2 e3 -> do
    result <- asks $ M.lookup x
    case result of
       Just Safe -> do
           t2 <- local (M.insert x SafeString) $ typeCheck e2
           t3 <- typeCheck e3
           return $ superType t2 t3
       otherwise -> checkIf c e2 e3
  EIf _ c e1 e2 ->
    case rejectCondition c of
      Just (c1, object, name) -> do
        -- object and name are strings taken from EId syntax nodes. They are
        -- safe. And you know this, man.
        typeCheck c1
        -- We can assume not only that name is safe, but that it is also a 
        -- safe string since it wasn't rejected, and reject() checks that it
        -- is a string.
        t1 <- local (M.insert name SafeString) $ typeCheck e1
        t2 <- typeCheck e2
        return $ superType t1 t2
      Nothing -> checkIf c e1 e2
  EObject a props -> do
    ts <- mapM typeCheck (map snd props)
    to <- foldM (\t' (s, t) -> if isBanned s then return t' else return $ superType t t') World (zip (map fst props) ts)
    case (sourceLine a, sourceColumn a) of
      (1478, 15) -> if subType to World then return to else error ("DOM wasn't type World" ++ (show (zip (map fst props) ts)))
      (760, 27) -> if subType to World then return to else error ("Bunch.prototype wasn't type World" ++ (show (zip (map fst props) ts)))
      (1602, 12) -> if subType to World then return to else error ("ADSAFE wasn't type World" ++ (show (zip (map fst props) ts)))
      otherwise -> return to
  EGetField _ e1 e2 -> do
    t1 <- typeCheck e1
    t2 <- typeCheck e2
    case t2 of
      Safe -> return World
      SafeString -> return World
      otherwise -> return JS
{-
      otherwise -> do
        field <- asks $ M.lookup "field"
        throwError $ "unsafe field lookup.\n" ++ 
                          "type of field is " ++ 
                          show field ++ "\n" ++
                          (pretty e2)
-}
  EUpdateField _ e1 e2 e3 -> do
    t1 <- typeCheck e1
    t2 <- typeCheck e2
    t3 <- typeCheck e3
    return (superType t1 t3) -- otherwise, the object could go from World->JS
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
          return World
        Nothing -> do
          put $ M.insert lbl te labs
          return World
  EThrow _ e -> typeCheck e
  EWhile _ e1 e2 -> do
    typeCheck e1
    typeCheck e2
    return JS
  ECatch _ e1 e2 -> do
    typeCheck e1
    typeCheck e2
    return JS
  EFinally _ e1 e2 -> do
    typeCheck e1
    typeCheck e2
    return JS
  EEval _ -> error "unexpected EEval"
  ELet1{} -> error "unexpected ELet1 (removeHOAS not called?)"
  ELet2{} -> error "unexpected ELet2 (removeHOAS not called?)"

rejectCondition :: Expr a -> Maybe (Expr a, Ident, Ident)
rejectCondition (EOp _ OPrimToBool 
                      [(ELet _ [("$lAnd", c1)] 
                        (EIf _ 
                            (EIf _ 
                                 (EOp _ OPrimToBool [(EId _ "$lAnd")])
                                 (EBool _ False)
                                 (EBool _ True))
                            (EId _ "$lAnd")
                            (EIf _ (EOp _ OPrimToBool 
                                        [(ELet _ [("$obj", (EDeref _ (EId _ "reject")))]
                                            (EIf _ _
                                                 _
                                                 (ELet _ [(_, EId _ "$obj")]
                                                    (EApp _ 
                                                          (EGetField _ 
                                                            (EDeref _ _)
                                                            (EString _ "$code"))
                                                        [ (EId _ "$global")
                                                        , (ERef _ (ERef _ (EObject _ [_, _, _, _, _, ("0", EId _ object), ("1", EId _ name)])))]))))])
                                   (EBool _ False)
                                   (EBool _ True))))]) = Just (c1, object, name)
rejectCondition _ = Nothing

checkIf c e1 e2 = do
  t1 <- typeCheck c
  t2 <- typeCheck e1
  t3 <- typeCheck e2
  return (superType t2 t3)

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
  , "URIError", "this", "$makeException"
  ]

isTypeable = runTyper . typeCheck . addGlobals . removeHOAS
  where addGlobals b = ELet nopos [(x, EUndefined nopos) | x <- globalEnv] b
        runTyper (Typer m) = runReaderT (evalStateT m M.empty) M.empty

