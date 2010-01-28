module BrownPLT.JavaScript.Semantics.ANF where

import BrownPLT.JavaScript.Semantics.Syntax
import Control.Monad.State

data Value a
  = VNumber a Double
  | VString a String
  | VBool a Bool
  | VUndefined a
  | VNull a
  | VId a Ident
  | VLambda a [Ident] (Exp a)


data BindExp a
  = BObject a [(String, Value a)]
  | BSetRef a (Value a) (Value a)
  | BRef a (Value a)
  | BDeref a (Value a)
  | BGetField a (Value a) (Value a)
  | BUpdateField a (Value a) (Value a) (Value a)
  | BDeleteField a (Value a) (Value a)
  | BValue a (Value a)
  | BOp a Op [Value a]
  | BApp a (Value a) [Value a]


data Exp a
  = ALet a ([Ident, BindExp a]) (Exp a)
  | AIf a (Value a) (Exp a) (Exp a)
  | ARec a ([Ident, Value a]) (Exp a)
  | ALabel a Label (Exp a)
  | ABreak a Label (Value a)
  | AThrow a (Value a)
  | ACatch a (Exp a) (Value a)
  | AFinally a (Exp a) (Exp a)
  | AReturn a (Value a)

type M a = State Int a

newVar :: M Ident
newVar = do
  n <- get
  put (n + 1)
  return ("$anf" ++ show n)


toANF :: Expr a
      -> (Value a -> M (Exp a))
      -> M (Exp a)
toANF expr k = case expr of
    ENumber a x -> k (VNumber a x)
  | EString a String
  | EBool a Bool
  | EUndefined a
  | ENull a
  | ELambda a [Ident] (Expr a)
  | EObject a [(String, (Expr a))]
  | EId a Ident
  | EOp a Op [Expr a]
  | EApp a (Expr a) [Expr a]
  | ELet a [(Ident, (Expr a))] (Expr a)
  | ESetRef a (Expr a) (Expr a)
  | ERef a (Expr a)
  | EDeref a (Expr a)
  | EGetField a (Expr a) (Expr a)
  | EUpdateField a (Expr a) (Expr a) (Expr a)
  | EDeleteField a (Expr a) (Expr a)
  | ESeq a (Expr a) (Expr a)
  If a e1 e2 e3 -> do
    toANF e1 (\v1 -> do
      e2' <- toANF e2 (\v2 -> return (AReturn a v2))
      e3' <- toANF e3 (\v3 -> return (AReturn a v3))
      return (AIf a v1 e2' e3'))
  EWhile a e1 e2 -> do
      f <- newVar
      e2' <- toANF e2 (\v2 -> do
        tmp1 <- newVar
        return (ALet a [(tmp1, BApp a (VId f))] (AReturn a (VId tmp1))))
      loopBody <- toANF e1 ( \v1 -> do
        return (AIf a v1 e2' (AReturn a (VUndefined a))))
      r <- newVar
      rest <- k (VId r)
      return $ ARec a ([f, VLambda [] loopBody])
                 (ALet a ([r, BApp a (VId f) []]) rest)
     


  | ELabel a Label (Expr a)
  | EBreak a Label (Expr a)
  | EThrow a (Expr a)
  | ECatch a (Expr a) (Expr a)
  | EFinally a (Expr a) (Expr a)
  -- |We use HOAS when possible so that we don't mess up bindings.  When
  -- pretty-printing, we unravel these to use conventional bindings.
  | ELet1 a (Expr a) (Ident -> (Expr a))
  | ELet2 a (Expr a) (Expr a) (Ident -> Ident -> (Expr a))
  | EEval a -- ^an expression that calls eval, or a related function.  If
            -- EEval becomes the active expression, our model immediately aborts.
