module BrownPLT.JavaScript.Analysis.MergeSequences
    ( mergeSeqs ) where

import Data.Generics

import BrownPLT.JavaScript.Semantics.Syntax
import BrownPLT.JavaScript.Semantics.ANF ( Value(..), BindExp(..), Exp(..) )
import BrownPLT.JavaScript.Semantics.Prelude

mergeSeqs :: forall a c. (Data a, Data (c a)) => c a -> c a
mergeSeqs = everywhere' (mkT (mergeSeqsExp :: Exp a -> Exp a)
                          `extT` (mergeSeqsVal :: Value a -> Value a)
                          `extT` (mergeSeqsBind :: BindExp a -> BindExp a))

merge :: (Data a) => (Exp a -> Exp a) -> Exp a -> Exp a -> Exp a
merge k e1 e2 =
    case e1 of
      ALet a binds body -> merge (\e -> (k (ALet a binds e))) body e2
      AReturn a v -> 
          (k (ALet a [("$UNUSED", (BValue a v))] e2))
      ABind a b ->
          (k (ALet a [("$UNUSED", b)] e2))
      otherwise -> do
              ASeq (label e1) (k e1) e2

mergeSeqsExp :: forall a c. (Data a) => Exp a -> Exp a
mergeSeqsExp e =
    case e of
      ASeq a e1 e2 -> 
          merge id e1 e2
      otherwise -> e

mergeSeqsVal :: forall a c. (Data a) => Value a -> Value a
mergeSeqsVal (VLambda a xs e) =
    (VLambda a xs (mergeSeqsExp e))
mergeSeqsVal v = v


mergeSeqsBind :: forall a c. (Data a) => BindExp a -> BindExp a
mergeSeqsBind b =
    gmapT (mkT (mergeSeqsExp :: Exp a -> (Exp a))
           `extT` (mergeSeqsVal :: Value a -> (Value a))
           `extT` (mergeSeqsBind :: BindExp a -> (BindExp a))
           `extT` (mergeSeqsValLst :: [Value a] -> [Value a])
           `extT` (mergeSeqsValMap  
                   :: [(String, Value a)] -> [(String, Value a)])) b

mergeSeqsValLst :: forall a c. (Data a) =>
                   [Value a] -> [Value a]
mergeSeqsValLst vs = map mergeSeqsVal vs

mergeSeqsValMap :: forall a c. (Data a) => 
                   [(String, Value a)] -> 
                   [(String, Value a)]
mergeSeqsValMap ps =
    map (\(s,v) -> (s, mergeSeqsVal v)) ps

      
