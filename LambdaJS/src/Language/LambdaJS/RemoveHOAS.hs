module Language.LambdaJS.RemoveHOAS
  ( removeHOAS
  ) where

import Control.Monad.State
import Control.Monad
import Language.LambdaJS.Syntax


type M a = State Int a


newVar :: M Ident
newVar = do
  n <- get
  put (n + 1)
  return ("$" ++ show n)


expr :: Expr a -> M (Expr a)
expr e = case e of
  ENumber a _ -> return e
  EString a _ -> return e
  EBool a _ -> return e
  EUndefined a -> return e
  ENull a -> return e
  ELambda a xs e1 -> liftM (ELambda a xs) (expr e1)
  EObject a props -> do
    vals <- mapM expr (map snd props)
    return (EObject a (zip (map fst props) vals))
  EId a _ -> return e
  EOp a op es -> liftM (EOp a op) (mapM expr es)
  EApp a e1 es -> liftM2 (EApp a) (expr e1) (mapM expr es)
  ELet a binds e1 -> do
    vals <- mapM expr (map snd binds)
    e1' <- expr e1
    return (ELet a (zip (map fst binds) vals) e1')
  ELet1 a e1 f -> do
    x <- newVar
    e1' <- expr e1
    e2' <- expr (f x)
    return (ELet a [(x, e1')] e2')
  ELet2 a e1 e2 f -> do
    x <- newVar
    y <- newVar
    e1' <- expr e1
    e2' <- expr e2
    e3' <- expr (f x y)
    return (ELet a [(x, e1'), (y, e2')] e3')
  ESetRef a e1 e2 -> liftM2 (ESetRef a) (expr e1) (expr e2)
  ERef a e1 -> liftM (ERef a) (expr e1)
  EDeref a e1 -> liftM (EDeref a) (expr e1)
  EGetField a e1 e2 -> liftM2 (EGetField a) (expr e1) (expr e2)
  EDeleteField a e1 e2 -> liftM2 (EDeleteField a) (expr e1) (expr e2)
  EUpdateField a e1 e2 e3 -> liftM3 (EUpdateField a) (expr e1) (expr e2) (expr e3)
  ESeq a e1 e2 -> liftM2 (ESeq a) (expr e1) (expr e2)
  EIf a e1 e2 e3 -> liftM3 (EIf a) (expr e1) (expr e2) (expr e3)
  EWhile a e1 e2 -> liftM2 (EWhile a) (expr e1) (expr e2)
  ELabel a lbl e1 -> liftM (ELabel a lbl) (expr e1)
  EBreak a lbl e1 -> liftM (EBreak a lbl) (expr e1)
  EThrow a e1 -> liftM (EThrow a) (expr e1)
  ECatch a e1 e2 -> liftM2 (ECatch a) (expr e1) (expr e2)
  EFinally a e1 e2 -> liftM2 (EFinally a) (expr e1) (expr e2)
  EEval a -> return e


removeHOAS :: Expr a -> Expr a
removeHOAS e = evalState (expr e) 0
