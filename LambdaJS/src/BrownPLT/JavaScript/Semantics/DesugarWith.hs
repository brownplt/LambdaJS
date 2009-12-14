-- |Removes all 'WithStmt's.
--
-- A @with@ statement seems to break lexical scope, since it adds an arbitrary
-- object to the \"scope chain\":
--
-- @
-- function() {
--   var x = 10, y;
--   with (obj) {
--     x = 50; // if obj.hasOwnProperty("x"), then obj.x = 50, else x = 50
--     y = x // assume !obj.hasOwnProperty("y").  Same as above.
--   }
-- }
-- @
--
-- As the comments suggest, @with@ does not preclude lexical scope.  But, it
-- does preclude /closed programs/.  If we admit @with@, then our programs may
-- have free variables.
--
-- It is easy to macro-expand the example above.  Nested @with@s very similar.
-- We macro-expand inside out:
--
-- @
-- with (obj1) {
--   with (obj2) {
--     x = 50; // inner: check if obj2.hasOwnProperty("x"), else x is lexical
--             // outer: for lexical x, check if obj1.hasOwnProperty("x"),
--             //        else x is lexical
-- @
module BrownPLT.JavaScript.Semantics.DesugarWith (desugarWith) where

import qualified Data.Set as S
import BrownPLT.JavaScript.Semantics.Syntax

type Env = S.Set Ident

-- |We first desugar, then desugar @with@, since desugared ASTs are simpler.
-- 
expr :: Ident -> Env -> Expr -> Expr
expr wId env e = case e of
  ENumber _ -> e
  EString _ -> e
  EBool _ -> e
  EUndefined -> e
  ENull -> e
  ELambda args e -> ELambda args (expr wId env' e)
    where env' = (S.fromList args) `S.union` env
  EObject binds -> EObject (map f binds)
    where f (x, e2) = (x, expr wId env e2)
  EGetField (EDeref (EId "$global")) (EString x) ->
    EIf (EOp OHasOwnProp [EDeref $ EId wId, EString x])
        (EGetField (EDeref $ EId wId) (EString x))
        -- Preserve the $global["x"], so that an outer with can macro-expand
        -- the same way.
        (EGetField (EDeref (EId "$global")) (EString x))
  EDeref (EId x) -> case x `S.member` env of
    True -> e
    False -> EIf (EOp OHasOwnProp [EDeref $ EId wId, EString x])
                 -- We're re
                 (EGetField (EDeref $ EId wId) (EString x))
                 (EDeref $ EId x)
  EId x -> e
  EOp op es -> EOp op (map (expr wId env) es)
  EApp e es -> EApp (expr wId env e) (map (expr wId env) es)
  ELet binds body -> ELet (map f binds) (expr wId env' body)
    where f (x, e') = (x, expr wId env e')
          env' = (S.fromList (map fst binds)) `S.union` env
  ELet1 e1 f -> ELet1 (expr wId env e1) $ \x -> expr wId (S.insert x env) (f x)
  ELet2 e1 e2 f -> 
    ELet2 (expr wId env e1) (expr wId env e2) $ \x y -> 
      expr wId (S.insert y (S.insert x env)) (f x y)
  ESetRef (EId "$global") 
          (EUpdateField (EDeref (EId "$global")) (EString x) e) ->
    EIf (EOp OHasOwnProp [EDeref $ EId wId, EString x])
        (ESetRef (EId wId) 
                 (EUpdateField (EDeref (EId wId)) (EString x) (expr wId env e)))
        -- Preserve the $global[x] = e, so that an outer with can macro-expand
        -- the same way.
        (ESetRef (EId "$global") 
                 (EUpdateField (EDeref (EId "$global")) 
                               (EString x) 
                               (expr wId env e)))
  ESetRef (EId x) rhs -> case x `S.member` env of
    True -> e
    False -> EIf (EOp OHasOwnProp [EDeref $ EId wId, EString x])
     (ESetRef (EId wId) (EUpdateField (EDeref $ EId wId) (EString x) 
                                      (expr wId env rhs)))
     (ESetRef (EId x) (expr wId env rhs))
  ESetRef e1 e2 -> ESetRef (expr wId env e1) (expr wId env e2)
  ERef e1 -> ERef (expr wId env e1)
  EDeref e1 -> EDeref (expr wId env e1)
  EGetField e1 e2 -> EGetField (expr wId env e1) (expr wId env e2)
  EUpdateField e1 e2 e3 ->
    EUpdateField (expr wId env e1) (expr wId env e2) (expr wId env e3)
  ESeq e1 e2 -> ESeq (expr wId env e1) (expr wId env e2)
  EIf e1 e2 e3 -> EIf (expr wId env e1) (expr wId env e2) (expr wId env e3)
  EWhile e1 e2 -> EWhile (expr wId env e1) (expr wId env e2)
  ELabel lbl e1 -> ELabel lbl (expr wId env e1)
  EBreak lbl e1 -> EBreak lbl (expr wId env e1)
  EThrow e1 -> EThrow (expr wId env e1)
  ECatch e1 e2 -> ECatch (expr wId env e1) (expr wId env e2)
  EFinally e1 e2 -> EFinally (expr wId env e1) (expr wId env e2)
  EDeleteField e1 e2 -> EDeleteField (expr wId env e1) (expr wId env e2)
  EEval -> e

desugarWith :: Expr -- ^arbitrary object added to the \"scope chain\"
            -> Expr 
            -> Expr
desugarWith obj body = ELet1 obj $ \wId -> expr wId S.empty body
