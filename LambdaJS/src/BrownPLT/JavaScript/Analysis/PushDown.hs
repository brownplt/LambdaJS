module BrownPLT.JavaScript.Analysis.PushDown
    (
     pushDown
    ) where

import BrownPLT.JavaScript.Semantics.ANF
import BrownPLT.JavaScript.Semantics.Syntax

import BrownPLT.JavaScript.Analysis.FreeVars
import BrownPLT.JavaScript.Analysis.Pure

import Data.Generics

import qualified Data.Map as M
import qualified Data.Set as S



replaceIDVal :: forall a. (Data a) => Ident -> Ident -> Value a -> Value a
replaceIDVal x y v = 
    case v of
      VId a x' | x==x' -> (VId a y)
      VLambda a xs e -> if (S.member x (freeVars v)) then
                            (VLambda a xs (replaceIDExp x y e)) else
                            v
      otherwise -> v

replaceIDValLst :: forall a. (Data a) => Ident -> Ident -> [Value a] -> [Value a]
replaceIDValLst x y vs = map (replaceIDVal x y) vs

replaceIDValMap :: forall a. (Data a) => Ident -> Ident
                   -> [(String, Value a)] -> [(String, Value a)]
replaceIDValMap x y ps = map (\(s,v) -> (s, replaceIDVal x y v)) ps

replaceIDBind :: forall a. (Data a) => Ident -> Ident -> BindExp a -> BindExp a
replaceIDBind x y b = 
    gmapT (mkT   (replaceIDVal    x y :: Value   a  -> Value   a )
          `extT` (replaceIDExp    x y :: Exp     a  -> Exp     a )
          `extT` (replaceIDBind   x y :: BindExp a  -> BindExp a )
          `extT` (replaceIDValLst x y :: [Value  a] -> [Value  a])
          `extT` (replaceIDValMap x y
                      :: [(String, Value a)] -> [(String, Value a)])) b
    

replaceIDExp :: forall a. (Data a) => Ident -> Ident -> Exp a -> Exp a
replaceIDExp x y e = 
    case e of
      ALet a binds body | (any (\s -> s==x) (map fst binds)) -> e
      otherwise -> 
          gmapT (mkT    (replaceIDVal    x y :: Value   a  -> Value   a )
                 `extT` (replaceIDExp    x y :: Exp     a  -> Exp     a )
                 `extT` (replaceIDBind   x y :: BindExp a  -> BindExp a )
                 `extT` (replaceIDValLst x y :: [Value  a] -> [Value  a])
                 `extT` (replaceIDValMap x y
                      :: [(String, Value a)] -> [(String, Value a)])) e

replaceID :: forall a c. (Data a, Data (c a)) => Ident -> Ident -> c a -> c a
replaceID x y = everywhere (mkT   (replaceIDVal  x y :: Value   a -> Value   a)
                           `extT` (replaceIDExp  x y :: Exp     a -> Exp     a)
                           `extT` (replaceIDBind x y :: BindExp a -> BindExp a))


pushDownExp :: forall a. (Data a) => Exp a -> Exp a
pushDownExp e = 
    case e of
      ALet a [(x, (BValue _ (VId _ y)))] body -> replaceID x y body
      otherwise -> e

pushDown :: forall a c. (Data a, Data (c a)) => c a -> c a
pushDown = everywhere (mkT (pushDownExp :: Exp a -> Exp a))