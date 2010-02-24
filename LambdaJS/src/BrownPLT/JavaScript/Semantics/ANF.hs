module BrownPLT.JavaScript.Semantics.ANF 
    ( Value(..)
    , BindExp(..)
    , Exp(..)
    , toANF  
    , exprToANF
    ) where

import Control.Monad.State

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

type M a = State Int a

-- Is the LambdaJS expression a value? Note that object literals are not 
-- considered values.
--
isValue :: Data a => Expr a -> Bool
isValue = maybe False (const True) . exprToValue

-- Turn an Expr into a 'Value' if possible.
--
exprToValue :: Data a => Expr a -> Maybe (M (Value a))
exprToValue e = case e of
  ENumber a d -> jr $ VNumber a d
  EString a s -> jr $ VString a s
  EBool   a b -> jr $ VBool   a b

  EUndefined a -> jr $ VUndefined a
  ENull      a -> jr $ VNull a

  ELambda a as b -> Just $ do
    b' <- toANF b $ \v -> return $ AReturn a v
    return $ VLambda a as b'
  
  EId a id  -> jr $ VId a id
  EEval a   -> jr $ VEval a
  otherwise -> Nothing
  where jr = Just . return 

-- Is the LambdaJS expression a BindExpr without additional ANFing?
--
isBindExp :: Data a => Expr a -> Bool
isBindExp = maybe False (const True) . exprToBindExp

-- Is an expression an object literal whose fields are all values?
--
-- TODO: This code could benefit from some applicative style.
--
exprToBindExp :: Data a => Expr a -> Maybe (M (BindExp a))
exprToBindExp e = case e of
  ERef    a e' ->
    case exprToValue e' of
      Just mv -> Just $ do { v <- mv; return $ BRef a v }
      Nothing -> Nothing
  EDeref  a e' ->
    case exprToValue e' of
      Just mv -> Just $ do { v <- mv; return $ BDeref a v }
      Nothing -> Nothing
  EObject a fs -> 
    case mapM (exprToValue . snd) fs of
      Just vs -> Just $ do
        vs' <- sequence vs
        return $ BObject a (zip (map fst fs) vs')
      Nothing -> Nothing
  otherwise -> Nothing


newVar :: M Ident
newVar = do
  n <- get
  put (n + 1)
  return ("$anf" ++ show n)


toANFMany :: Data a
          => [Expr a]
          -> ([Value a] -> M (Exp a))
          -> M (Exp a)
toANFMany [] k = k []
toANFMany (e:es) k = 
    toANF e (\v -> do
               rest <- toANFMany es (\xs -> k (v:xs))
               return rest)

toANFManyForLet :: Data a
                => [Expr a]
                -> ([Either (Value a) (BindExp a)] -> M (Exp a))
                -> M (Exp a)
toANFManyForLet []     k = k []
toANFManyForLet (e:es) k
  | isBindExp e = do
      b <- fromJust $ exprToBindExp e
      toANFManyForLet es $ \xs -> k $ (Right b):xs
  | otherwise = do
      toANF e $ \v -> toANFManyForLet es $ \xs -> k $ (Left v):xs


toANF :: Data a
      => Expr a
      -> (Value a -> M (Exp a))
      -> M (Exp a)
toANF expr k =
    case expr of
      ENumber a d -> k (VNumber a d)
      EString a s -> k (VString a s)
      EBool   a b -> k (VBool a b)
      EUndefined a -> k (VUndefined a)
      ENull a -> k (VNull a)
      EId a x -> k (VId a x)
      ELambda a args body -> do
                abody <- (toANF body (\v -> return (AReturn a v)))
                k (VLambda a args abody)
      EObject a binds -> let names = map fst binds
                             fields = map snd binds in
                         do
                           toANFMany fields (\vfields -> do
                                               x <- newVar
                                               rest <- k (VId a x)
                                               return (ALet a [(x, BObject a (zip names vfields))] rest))
      EOp a op args -> toANFMany args (\vargs -> do
                                           x <- newVar 
                                           rest <- k (VId a x)
                                           return (ALet a [(x, BOp a op vargs)] rest))
      EApp a func args -> toANF func (\vfunc ->
                                        toANFMany args (\vargs -> do
                                                          x <- newVar
                                                          rest <- k (VId a x)
                                                          return (ALet a [(x, BApp a vfunc vargs)] rest)))
      -- Is this bad nesting of lets?  I'm not sure...
      ELet a binds body -> 
        let (names, vals) = unzip binds
          in toANFManyForLet vals $ \vals' -> do
               let vals'' = map (either (BValue a) id) vals'
               body' <- toANF body k
               return $ ALet a (zip names vals'') body'
      ESetRef a id e -> toANF e (\v -> do
                                    x <- newVar
                                    rest <- k (VId a x)
                                    return (ALet a [(x, (BSetRef a id v))] rest))
      ERef a e -> toANF e (\v -> do 
                             x <- newVar
                             rest <- k (VId a x)
                             return (ALet a [(x, (BRef a v))] rest))
      EDeref a e -> toANF e (\v -> do 
                               x <- newVar 
                               rest <- k (VId a x)
                               return (ALet a [(x, (BDeref a v))] rest))
      EGetField a obj name -> toANF obj (\vobj -> 
                                         toANF name (\vname -> do
                                                       x <- newVar
                                                       rest <- k (VId a x)
                                                       return (ALet a [(x, (BGetField a vobj vname))] rest)))
      EUpdateField a obj name val -> toANF
                                     obj
                                     (\vobj -> toANF 
                                               name 
                                               (\vname -> toANF
                                                          val
                                                          (\vval -> do
                                                             x <- newVar
                                                             rest <- k (VId a x)
                                                             return (ALet a [(x, (BUpdateField a vobj vname vval))] rest))))
      EDeleteField a obj name -> toANF obj (\vobj -> 
                                            toANF name (\vname -> do
                                                            x <- newVar
                                                            rest <- k (VId a x)
                                                            return (ALet a [(x, (BDeleteField a vobj vname))] rest)))
      ESeq a e rest -> do
                e' <- toANF e (\v -> return (AReturn a v))
                rest' <- toANF rest k
                return (ASeq a e' rest')
      EIf a e1 e2 e3 -> do
              toANF e1 (\v1 -> do
                          x <- newVar
                          rest <- k (VId a x)
                          e2' <- toANF e2 (\v2 -> return (AReturn a v2))
                          e3' <- toANF e3 (\v3 -> return (AReturn a v3))
                          return (ALet a [(x, (BIf a v1 e2' e3'))] rest))
      EWhile a e1 e2 -> do
                f <- newVar
                e2' <- toANF e2 (\v2 -> do
                                   tmp1 <- newVar
                                   recfunc <- newVar
                                   return (ALet a [(recfunc, (BDeref a (VId a f)))]
                                           (ALet a [(tmp1, (BApp a (VId a recfunc) []))] (AReturn a (VId a tmp1)))))
                loopBody <- toANF e1 (\v1 -> do
                                        return (ABind a (BIf a v1 e2' (AReturn a (VUndefined a)))))
                r <- newVar
                t <- newVar
                unused <- newVar
                func <- newVar
                rest <- k (VId a r)
                return $ ALet a [(f, (BRef a (VUndefined a)))]
                           (ALet a [(t, (BValue a (VLambda a [] loopBody)))]
                            (ALet a [(unused, (BSetRef a f (VId a t)))]
                             (ALet a [(func,  (BDeref a (VId a f)))]
                              (ALet a [(r, BApp a (VId a func) [])] rest))))
      ELabel a l e -> do
                body <- toANF e k
                return (ALabel a l body)
      EBreak a l e ->
          toANF e (\v -> return (ABreak a l v))
      EThrow a e ->
          toANF e (\v -> return (AThrow a v))
      ECatch a body func -> do
          body' <- toANF body k
          toANF func (\vfunc ->
                          return (ACatch a body' vfunc))
      EFinally a body rest -> do
          body' <- toANF body k
          rest' <- toANF rest (\v -> return (AReturn a v))
          return (AFinally a body' rest')
      ELet1 a e1 e2 -> return (AReturn (label e1) (VString (label e1) "ELet1 shouldn't be here"))
      ELet2 a e1 e2 e3 -> return (AReturn (label e1) (VString (label e1) "ELet2 shouldn't be here"))
      EEval a ->  k (VEval a)


exprToANF :: Data a => Expr a -> Exp a
exprToANF e = evalState (toANF (removeHOAS e) (\v -> (return (AReturn (label e) v)))) 0
