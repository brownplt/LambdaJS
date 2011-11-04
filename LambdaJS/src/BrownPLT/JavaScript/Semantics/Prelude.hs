module BrownPLT.JavaScript.Semantics.Prelude
  ( collectExclude
  , everywhereUpto
  , everythingUpto
  , SourcePos
  , Set
  ) where

import Data.Generics
import Data.Set (Set)
import Text.ParserCombinators.Parsec.Pos (SourcePos, initialPos)

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
