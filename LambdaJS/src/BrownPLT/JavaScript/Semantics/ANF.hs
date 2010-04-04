module BrownPLT.JavaScript.Semantics.ANF 
    ( Value(..)
    , BindExp(..)
    , Exp(..)
    , toANF  
    , exprToANF
    ) where

import Control.Monad.State

import Data.Generics

import Data.Maybe ( fromJust, maybe )
import Data.Either ( either )

import System.IO.Unsafe

import BrownPLT.JavaScript.Semantics.Syntax
import BrownPLT.JavaScript.Semantics.Prelude
import BrownPLT.JavaScript.Semantics.RemoveHOAS


data Value a
  = VNumber a Double
  | VString a String
  | VBool a Bool
  | VUndefined a
  | VNull a
  | VId a Ident
  | VLambda a [Ident] (Exp a)
  | VEval a
    deriving (Show, Data, Typeable)


data BindExp a
  = BObject a [(String, Value a)]
  | BSetRef a Ident (Value a)
  | BRef a (Value a)
  | BDeref a (Value a)
  | BGetField a (Value a) (Value a)
  | BUpdateField a (Value a) (Value a) (Value a)
  | BDeleteField a (Value a) (Value a)
  | BValue a (Value a)
  | BOp a Op [Value a]
  | BApp a (Value a) [Value a]
  | BIf a (Value a) (Exp a) (Exp a)
    deriving (Show, Data, Typeable)

data Exp a
  = ALet a [(Ident, BindExp a)] (Exp a)
  | ASeq a (Exp a) (Exp a)
  | ALabel a Label (Exp a)
  | ABreak a Label (Value a)
  | AThrow a (Value a)
  | ACatch a (Exp a) (Value a)
  | AFinally a (Exp a) (Exp a)
  | AReturn a (Value a)
  | ABind a (BindExp a)
    deriving (Show, Data, Typeable)

type M a = State (String, Int) a

type ANFKont a  = Either (Value a) (BindExp a) -> M (Exp a)
type ANFsKont a = [Either (Value a) (BindExp a)] -> M (Exp a)
type ValKont a  = Value a -> M (Exp a)
type ValsKont a = [Value a] -> M (Exp a)

newVar :: M Ident
newVar = do
  (s, n) <- get
  put (s, (n + 1))
  return (s ++ show n)

toExp (Left  v) = AReturn (label v) v
toExp (Right b) = ABind   (label b) b

toExp' :: a -> Either (Value a) (BindExp a) -> Exp a
toExp' a e = either (AReturn a) (ABind a) e

toValue :: Data a => Either (Value a) (BindExp a) -> ValKont a -> M (Exp a)
toValue (Left  v) k = k v
toValue (Right b) k = do
  x <- newVar 
  e <- k $ VId (label b) x
  return $ ALet (label b) [(x, b)] e

toValues :: Data a => [Either (Value a) (BindExp a)] -> ValsKont a -> M (Exp a)
toValues []     k = k []
toValues (v:vs) k =
  toValue v $ \v' -> toValues vs $ \vs' -> k (v':vs')

toANFValue :: Data a => Expr a -> ValKont a -> M (Exp a)
toANFValue e k = toANF e $ \e' -> toValue e' k

toANFValues :: Data a => [Expr a] -> ValsKont a -> M (Exp a)
toANFValues es k = toANFMany es $ \es' -> toValues es' k

toANFMany :: Data a => [Expr a] -> ANFsKont a -> M (Exp a)
toANFMany [] k = k []
toANFMany (e:es) k = 
    toANF e $ \v -> toANFMany es $ \xs -> k (v:xs)

toANF :: Data a => Expr a -> ANFKont a -> M (Exp a)
toANF expr k =
    case expr of
      ENumber a d -> k $ Left $ VNumber a d
      EString a s -> k $ Left $ VString a s
      EBool   a b -> k $ Left $ VBool a b
      EUndefined a -> k $ Left $ VUndefined a
      ENull a -> k $ Left $ VNull a
      EId a x -> k $ Left $ VId a x
      ELambda a args body -> do
        abody <- toANF body $ \vb -> return $ toExp' a vb
        k $ Left $ VLambda a args abody
      EObject a binds -> 
        let (ns, fs) = unzip binds
          in toANFValues fs $ \vs -> k $ Right $ BObject a (zip ns vs)
      EOp a op args -> toANFValues args (\vargs -> k $ Right (BOp a op vargs))
      EApp a func args -> toANFValue func (\vfunc ->
                                               toANFValues args (\vargs -> k $ Right (BApp a vfunc vargs)))
      ELet a binds body -> 
        let (ns, bs) = unzip binds
          in do
            body' <- toANF body k
            toANFValues bs $ \vbs -> do
              let vbs' = map (BValue a) vbs
              return $ ALet a (zip ns vbs') body'
      ESetRef a ident e -> 
          toANFValue e (\v -> k $ Right (BSetRef a ident v))
      ERef a e ->
          toANFValue e $ \v -> k $ Right $ BRef a v
      EDeref a e ->
          toANFValue e $ \v -> k $ Right $ BDeref a v
      EGetField a obj name -> toANFValue obj (\vobj -> 
                                         toANFValue name (\vname -> k $ Right (BGetField a vobj vname)))
      EUpdateField a obj name val -> toANFValue
                                     obj
                                     (\vobj -> toANFValue
                                               name 
                                               (\vname -> toANFValue
                                                          val
                                                          (\vval -> k $ Right (BUpdateField a vobj vname vval))))
      EDeleteField a obj name -> toANFValue obj (\vobj -> 
                                            toANFValue name (\vname -> k $ Right (BDeleteField a vobj vname)))
      ESeq a e1 e2 -> do
        e1' <- toANFValue e1 $ \v -> return (AReturn a v)
        e2' <- toANFValue e2 (\v -> k $ Left v)
        case e1' of
          AReturn _ _ -> return e2'
          otherwise   -> return $ ASeq a e1' e2'
      EIf a e1 e2 e3 -> do
        toANFValue e1 $ \v1 -> do
          e2' <- toANF e2 $ \v2 -> return (toExp' a v2)
          e3' <- toANF e3 $ \v3 -> return (toExp' a v3)
          k $ Right (BIf a v1 e2' e3')
      EWhile a e1 e2 -> do
                f <- newVar
                e2' <- toANFValue e2 (\v2 -> do
                                        tmp1 <- newVar
                                        recfunc <- newVar
                                        return (ALet a [(recfunc, (BDeref a (VId a f)))]
                                                (ALet a [(tmp1, (BApp a (VId a recfunc) []))] (AReturn a (VId a tmp1)))))
                loopBody <- toANFValue e1 (\v1 -> do
                                        return (ABind a (BIf a v1 e2' (AReturn a (VUndefined a)))))
                r <- newVar
                t <- newVar
                unused <- newVar
                func <- newVar
                rest <- k $ Left (VId a r)
                return $ ALet a [(f, (BRef a (VUndefined a)))]
                           (ALet a [(t, (BValue a (VLambda a [] loopBody)))]
                            (ALet a [(unused, (BSetRef a f (VId a t)))]
                             (ALet a [(func,  (BDeref a (VId a f)))]
                              (ALet a [(r, BApp a (VId a func) [])] rest))))
      ELabel a l e -> do
        body <- toANF e k
        return (ALabel a l body)
      EBreak a l e ->
        toANFValue e (\v -> return (ABreak a l v))
      EThrow a e ->
        toANFValue e (\v -> return (AThrow a v))
      ECatch a body func -> do
       body' <- toANF body k
       toANFValue func $ \vfunc -> return $ ACatch a body' vfunc
      EFinally a body rest -> do
        body' <- toANF body k
        rest' <- toANF rest $ \v -> return $ toExp' a v
        return $ AFinally a body' rest'
      ELet1 a e1 e2 -> return (AReturn (label e1) (VString (label e1) "ELet1 shouldn't be here"))
      ELet2 a e1 e2 e3 -> return (AReturn (label e1) (VString (label e1) "ELet2 shouldn't be here"))
      EEval a ->  k $ Left (VEval a)


exprToANF :: Data a => String -> Expr a -> Exp a
exprToANF s e = evalState (toANFValue (removeHOAS e) (\v -> (return (AReturn (label e) v)))) (s,0)
