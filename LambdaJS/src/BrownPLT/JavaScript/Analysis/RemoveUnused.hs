module BrownPLT.JavaScript.Analysis.RemoveUnused
    (
     removeUnused
    ) where

import BrownPLT.JavaScript.Semantics.ANF
import BrownPLT.JavaScript.Semantics.Syntax

import BrownPLT.JavaScript.Analysis.FreeVars
import BrownPLT.JavaScript.Analysis.Pure

import Data.Generics

import qualified Data.Map as M
import qualified Data.Set as S

{-
  
  Performs the simplification:
  
  (let [(x y)] body) => body
  
  When x isn't in the free vars of body, and y doesn't have any side effects.

-}

removeUnusedExp :: (Data a) => Exp a -> Exp a
removeUnusedExp e =
    case e of
      ALet a [(x, b)] body ->
          if (isPure b) && (S.notMember x (freeVars body)) then
              body else
              e
      otherwise -> e

removeUnused :: forall a c. (Data a, Data (c a)) => c a -> c a
removeUnused = everywhere (mkT (removeUnusedExp :: Exp a -> Exp a))
