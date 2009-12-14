module BrownPLT.JavaScript.Semantics.Prelude
  ( collectExclude
  , everywhereUpto
  , everythingUpto
  , SourcePos
  , module Data.Generics
  , Set
  ) where

import Data.Generics
import Data.Set (Set)
import Text.ParserCombinators.Parsec.Pos (SourcePos, initialPos)

instance Typeable SourcePos where
  typeOf _  = 
    mkTyConApp (mkTyCon "Text.ParserCombinators.Parsec.Pos.SourcePos") []

 
-- Complete guesswork.  It seems to work.
-- This definition is incomplete.
instance Data SourcePos where
  -- We treat source locations as opaque.  After all, we don't have access to
  -- the constructor.
  gfoldl k z pos = z pos
  toConstr _ = sourcePosConstr1 where
    sourcePosConstr1 = mkConstr sourcePosDatatype "SourcePos" [] Prefix
    sourcePosDatatype = mkDataType "SourcePos" [sourcePosConstr1]
  gunfold   = error "gunfold is not defined for SourcePos"
  dataTypeOf = error "dataTypeOf is not defined for SourcePos"


collectExclude :: Data r
               => GenericQ Bool -- ^descend into a subtree?
               -> (r -> Bool) -- ^return the node?
               -> GenericQ [r]
collectExclude canDescend doReturn x = case canDescend x of
  False -> []
  True -> 
    (mkQ [] f x) ++ (concat $ gmapQ (collectExclude canDescend doReturn) x)
      where f r = case doReturn r of
                    True -> [r]
                    False -> []

-- | Similar to 'everything', but only applies the query to nodes that satisfy
-- the predicate.  We do apply the query when 'canDescend' is 'False', but we
-- do not recur.
--
-- It is possible to do approximately the same operation with 'everything', but
-- this interface is a lot simpler.
everythingUpto :: GenericQ Bool -- ^descend into a subtree?
               -> (r -> r -> r)
               -> GenericQ r
               -> GenericQ r
everythingUpto canDescend combine query x = case canDescend x of
  False -> query x
  True -> foldl combine 
               (query x) 
               (gmapQ (everythingUpto canDescend combine query) x)


-- | Descends into all nodes that satisfy the predicate.  The transformer
-- is applied to all nodes, including nodes at which descent stops.
everywhereUpto :: GenericQ Bool -> GenericT -> GenericT
everywhereUpto q f x = case q x of
  True -> f x
  False -> f (gmapT (everywhereUpto q f) x)
