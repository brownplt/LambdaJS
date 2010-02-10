module BrownPLT.JavaScript.ADsafe.Transformation
    ( flattenSeqs
    , rewriteErrors
    , adsafeTransform
    ) where

import BrownPLT.JavaScript.Semantics.Syntax
import BrownPLT.JavaScript.Semantics.Desugar ( desugar )
import BrownPLT.JavaScript.Parser ( parseScriptFromString )

import Data.Generics

-- Note: For correctness this must be done in two phases; they cannot be
-- interleaved, i.e., combined with extT.
--
adsafeTransform :: Data a => Expr a -> Expr a
adsafeTransform = rewriteErrors . flattenSeqs

-- Eliminate tree-structure that may arise from desugaring nested block
-- statements. Note: This needs to be applied top-down.
--
--     s        s
--    / \      / \
--   s   x    z   s
--  / \          / \
-- z   y        y   x
--
flattenSeqs :: forall a. Data a => Expr a -> Expr a
flattenSeqs = everywhere' $ mkT (flattenSeq :: Expr a -> Expr a)
  where
    flattenSeq (ESeq a1 (ESeq a2 e1 e2) e3) = flattenSeq $ ESeq a1 e1 (ESeq a2 e2 e3)
    flattenSeq e                            = e

-- Put the continuation of an if whose true branch is an error call into the
-- false branch.
--
rewriteErrors :: forall a. Data a => Expr a -> Expr a
rewriteErrors = everywhere $ mkT (rewriteError :: Expr a -> Expr a)
  where
    rewriteError (ESeq _ (EIf a c t (EUndefined _)) e2) | isError t = EIf a c t e2
    rewriteError e                                                  = e

isError :: Data a => Expr a -> Bool
isError (EBreak _ "$return"
            (ELet _ [("$obj", EDeref _ (EId _ "error"))]
              (EIf _ _
                 (EThrow _ (EApp _ (EId _ "$makeException")
                           [ EString _ "TypeError"
                           , EString _ ":CallExpr given non-function"
                           ]))
                 (ELet _ [(_, (EId _ "$obj"))] _)))) = True
isError _ = False
