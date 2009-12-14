module BrownPLT.JavaScript.Semantics.FreeVars
  ( freeVars
  ) where

import BrownPLT.JavaScript.Semantics.Prelude
import BrownPLT.JavaScript.Syntax
import BrownPLT.JavaScript.Environment (env)
import qualified Data.Map as M


freeVars :: Statement SourcePos -> [String]
freeVars s = M.keys varMap
  where (_, varMap) = env M.empty [s]