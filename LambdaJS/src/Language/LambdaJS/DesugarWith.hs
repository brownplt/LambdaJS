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
module Language.LambdaJS.DesugarWith (desugarWith) where

import qualified Data.Set as S
import Language.LambdaJS.Syntax

type Env = S.Set Ident

-- |We first desugar, then desugar @with@, since desugared ASTs are simpler.
-- 
expr :: Ident -> Env -> Expr a -> Expr a
expr wId env e = case e of
  ENumber a _ -> e
  EString a _ -> e
  EBool a _ -> e
  EUndefined a -> e
  ENull a -> e
  ELambda a args e -> ELambda a args (expr wId env' e)
    where env' = (S.fromList args) `S.union` env
  EObject a binds -> EObject a (map f binds)
    where f (x, e2) = (x, expr wId env e2)
  EGetField a1 (EDeref a2 (EId a3 "$global")) (EString a4 x) ->
    EIf a1 (EOp a1 OHasOwnProp [EDeref a1 $ EId a1 wId, EString a4 x])
        (EGetField a1 (EDeref a1 $ EId a1 wId) (EString a4 x))
        -- Preserve the $global["x"], so that an outer with can macro-expand
        -- the same way.
        (EGetField a1 (EDeref a1 (EId a1 "$global")) (EString a4 x))
  EDeref a1 (EId a2 x) -> case x `S.member` env of
    True -> e
    False -> EIf a1 (EOp a1 OHasOwnProp [EDeref a1 $ EId a2 wId, EString a2 x])
                 -- We're re
                 (EGetField a1 (EDeref a1 $ EId a2 wId) (EString a2 x))
                 (EDeref a1 $ EId a2 x)
  EId a x -> e
  EOp a op es -> EOp a op (map (expr wId env) es)
  EApp a e es -> EApp a (expr wId env e) (map (expr wId env) es)
  ELet a binds body -> ELet a (map f binds) (expr wId env' body)
    where f (x, e') = (x, expr wId env e')
          env' = (S.fromList (map fst binds)) `S.union` env
  ELet1 a e1 f -> ELet1 a (expr wId env e1) $ \x -> expr wId (S.insert x env) (f x)
  ELet2 a e1 e2 f -> 
    ELet2 a (expr wId env e1) (expr wId env e2) $ \x y -> 
      expr wId (S.insert y (S.insert x env)) (f x y)
  ESetRef a1 (EId a2 "$global") 
          (EUpdateField a3 (EDeref a4 (EId a5 "$global")) (EString a6 x) e) ->
    EIf a1 (EOp a3 OHasOwnProp [EDeref a4 $ EId a5 wId, EString a6 x])
        (ESetRef a3 (EId a5 wId) 
                     (EUpdateField a3 (EDeref a4 (EId a5 wId)) (EString a6 x) (expr wId env e)))
        -- Preserve the $global[x] = e, so that an outer with can macro-expand
        -- the same way.
        (ESetRef a3 (EId a5 "$global") 
                     (EUpdateField a3 (EDeref a4 (EId a5 "$global")) 
                                       (EString a6 x) 
                                       (expr wId env e)))
  ESetRef a1 (EId a2 x) rhs -> case x `S.member` env of
    True -> e
    False -> EIf a1 (EOp a1 OHasOwnProp [EDeref a1 $ EId a2 wId, EString a2 x])
     (ESetRef a1 (EId a2 wId) (EUpdateField a1 (EDeref a1 $ EId a2 wId) (EString a2 x) 
                                      (expr wId env rhs)))
     (ESetRef a1 (EId a2 x) (expr wId env rhs))
  ESetRef a e1 e2 -> ESetRef a (expr wId env e1) (expr wId env e2)
  ERef a e1 -> ERef a (expr wId env e1)
  EDeref a e1 -> EDeref a (expr wId env e1)
  EGetField a e1 e2 -> EGetField a (expr wId env e1) (expr wId env e2)
  EUpdateField a e1 e2 e3 ->
    EUpdateField a (expr wId env e1) (expr wId env e2) (expr wId env e3)
  ESeq a e1 e2 -> ESeq a (expr wId env e1) (expr wId env e2)
  EIf a e1 e2 e3 -> EIf a (expr wId env e1) (expr wId env e2) (expr wId env e3)
  EWhile a e1 e2 -> EWhile a (expr wId env e1) (expr wId env e2)
  ELabel a lbl e1 -> ELabel a lbl (expr wId env e1)
  EBreak a lbl e1 -> EBreak a lbl (expr wId env e1)
  EThrow a e1 -> EThrow a (expr wId env e1)
  ECatch a e1 e2 -> ECatch a (expr wId env e1) (expr wId env e2)
  EFinally a e1 e2 -> EFinally a (expr wId env e1) (expr wId env e2)
  EDeleteField a e1 e2 -> EDeleteField a (expr wId env e1) (expr wId env e2)
  EEval a -> e

desugarWith :: Expr SourcePos -- ^arbitrary object added to the \"scope chain\"
            -> Expr SourcePos
            -> Expr SourcePos
desugarWith obj body = ELet1 nopos obj $ \wId -> expr wId S.empty body
