module BrownPLT.JavaScript.Semantics.RemoveHOAS
  ( removeHOAS
  ) where

import Control.Monad.State
import Control.Monad
import BrownPLT.JavaScript.Semantics.Syntax


type M a = State Int a


newVar :: M Ident
newVar = do
  n <- get
  put (n + 1)
  return ("$" ++ show n)


expr :: Expr -> M Expr
expr e = case e of
  ENumber _ -> return e
  EString _ -> return e
  EBool _ -> return e
  EUndefined -> return e
  ENull -> return e
  ELambda xs e1 -> liftM (ELambda xs) (expr e1)
  EObject props -> do
    vals <- mapM expr (map snd props)
    return (EObject (zip (map fst props) vals))
  EId _ -> return e
  EOp op es -> liftM (EOp op) (mapM expr es)
  EApp e1 es -> liftM2 EApp (expr e1) (mapM expr es)
  ELet binds e1 -> do
    vals <- mapM expr (map snd binds)
    e1' <- expr e1
    return (ELet (zip (map fst binds) vals) e1')
  ELet1 e1 f -> do
    x <- newVar
    e1' <- expr e1
    e2' <- expr (f x)
    return (ELet [(x, e1')] e2')
  ELet2 e1 e2 f -> do
    x <- newVar
    y <- newVar
    e1' <- expr e1
    e2' <- expr e2
    e3' <- expr (f x y)
    return (ELet [(x, e1'), (y, e2')] e3')
  ESetRef e1 e2 -> liftM2 ESetRef (expr e1) (expr e2)
  ERef e1 -> liftM ERef (expr e1)
  EDeref e1 -> liftM EDeref (expr e1)
  EGetField e1 e2 -> liftM2 EGetField (expr e1) (expr e2)
  EDeleteField e1 e2 -> liftM2 EDeleteField (expr e1) (expr e2)
  EUpdateField e1 e2 e3 -> liftM3 EUpdateField (expr e1) (expr e2) (expr e3)
  ESeq e1 e2 -> liftM2 ESeq (expr e1) (expr e2)
  EIf e1 e2 e3 -> liftM3 EIf (expr e1) (expr e2) (expr e3)
  EWhile e1 e2 -> liftM2 EWhile (expr e1) (expr e2)
  ELabel lbl e1 -> liftM (ELabel lbl) (expr e1)
  EBreak lbl e1 -> liftM (EBreak lbl) (expr e1)
  EThrow e1 -> liftM EThrow (expr e1)
  ECatch e1 e2 -> liftM2 ECatch (expr e1) (expr e2)
  EFinally e1 e2 -> liftM2 EFinally (expr e1) (expr e2)
  EEval -> return e


removeHOAS :: Expr -> Expr
removeHOAS e = evalState (expr e) 0