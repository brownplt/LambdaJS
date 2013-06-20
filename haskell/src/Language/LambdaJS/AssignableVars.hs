module Language.LambdaJS.AssignableVars
  ( assignableVars
  ) where

import Language.LambdaJS.Prelude
import Language.ECMAScript3.Syntax
import qualified Data.Set as S


data Partial
  = Partial (Set String) -- variables bound in this scope block
            (Set String) -- variables assigned to in this scope block
            [Partial]    -- enclosing scopes


empty :: Partial
empty = Partial S.empty S.empty []


assign :: String -> Partial
assign x = Partial S.empty (S.singleton x) []


decl :: Id SourcePos -> Partial
decl x = Partial (S.singleton (unId x)) S.empty []


nest :: Partial -> Partial
nest p = Partial S.empty S.empty [p]


(+++) :: Partial -> Partial -> Partial
(Partial bound1 assigned1 nested1) +++ (Partial bound2 assigned2 nested2) =
  Partial (bound1 `S.union` bound2) 
          (assigned1 `S.union` assigned2)
          (nested1 ++ nested2)


unions :: [Partial] -> Partial
unions = foldr (+++) empty


lvalue :: LValue SourcePos -> Partial
lvalue lv = case lv of
  LVar p x -> assign x
  LDot _ e _ -> expr e
  LBracket _ e1 e2 -> unions [expr e1, expr e2]


expr :: Expression SourcePos -> Partial
expr e = case e of
  StringLit _ _ -> empty
  RegexpLit _ _ _ _ -> empty
  NumLit _ _ -> empty
  IntLit _ _ -> empty
  BoolLit _ _ -> empty
  NullLit _ -> empty
  ArrayLit _ es -> unions (map expr es)
  ObjectLit _ props -> unions (map (expr.snd) props)
  ThisRef _ -> empty
  VarRef _ id -> empty
  DotRef _ e _ -> expr e
  BracketRef _ e1 e2 -> unions [expr e1, expr e2]
  NewExpr _ e1 es -> unions [expr e1, unions $ map expr es]
  PrefixExpr _ _ e -> expr e
  InfixExpr _ _ e1 e2 -> unions [expr e1, expr e2]
  CondExpr _ e1 e2 e3 -> unions [expr e1, expr e2, expr e3]
  AssignExpr _ _ lv e -> unions [lvalue lv, expr e]
  UnaryAssignExpr _ _ lv -> lvalue lv
  ListExpr _ es -> unions (map expr es)
  CallExpr _ e es -> unions [expr e, unions $ map expr es]
  FuncExpr _ _ args s -> nest $ unions [unions $ map decl args, stmts s]


caseClause :: CaseClause SourcePos -> Partial
caseClause cc = case cc of
  CaseClause _ e ss -> unions [expr e, unions $ map stmt ss]
  CaseDefault _ ss -> unions $ map stmt ss


catchClause :: CatchClause SourcePos -> Partial
catchClause (CatchClause _ id s) = nest $ decl id +++ stmt s


varDecl :: VarDecl SourcePos -> Partial
varDecl (VarDecl _ id Nothing) = decl id +++ assign (unId id)
varDecl (VarDecl _ id (Just e)) = decl id +++ assign (unId id) +++ expr e

 
forInit :: ForInit SourcePos -> Partial
forInit fi = case fi of
  NoInit -> empty
  VarInit ds -> unions $ map varDecl ds
  ExprInit e -> expr e 


forInInit :: ForInInit SourcePos -> Partial
forInInit (ForInVar id) = assign (unId id) +++ decl id
-- TODO(arjun): seriously? arbitrary l-value?
forInInit (ForInLVal lv) = lvalue lv

stmts = unions . map stmt
  
stmt :: Statement SourcePos -> Partial
stmt s = case s of
  BlockStmt _ ss -> unions $ map stmt ss
  EmptyStmt _ -> empty
  ExprStmt _ e -> expr e
  IfStmt _ e s1 s2 -> unions [expr e, stmt s1, stmt s2]
  IfSingleStmt _ e s -> unions [expr e, stmt s]
  SwitchStmt _ e cases -> unions [expr e, unions $ map caseClause cases]
  WhileStmt _ e s -> unions [expr e, stmt s]
  DoWhileStmt _ s e -> unions [stmt s, expr e]
  BreakStmt _ _ -> empty
  ContinueStmt _ _ -> empty
  LabelledStmt _ _ s -> stmt s
  ForInStmt _ fii e s -> unions [forInInit fii, expr e, stmt s]
  ForStmt _ fi  me1 me2 s -> 
    unions [forInit fi, maybe empty expr me1, maybe empty expr me2, stmt s]
  TryStmt _ s catches ms ->
    unions [stmt s, maybe empty catchClause catches, maybe empty stmt ms]
  ThrowStmt _ e -> expr e
  ReturnStmt _ me -> maybe empty expr me
  WithStmt _ e s -> unions [expr e, stmt s]
  VarDeclStmt _ decls -> unions $ map varDecl decls
  FunctionStmt _ fnId args s ->
    unions [decl fnId, nest $ unions [unions $ map decl args, stmts s]]


assignable :: Partial -> Set String
assignable (Partial bound assigned []) = assigned `S.difference` bound
assignable (Partial bound assigned nested) = 
  (assigned `S.union` (S.unions $ map assignable nested)) 
    `S.difference` bound


assignableVars :: Statement SourcePos -> Set String
assignableVars = assignable . stmt
