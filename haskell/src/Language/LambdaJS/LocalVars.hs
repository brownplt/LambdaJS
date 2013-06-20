module Language.LambdaJS.LocalVars
  ( localVars
  ) where

import Language.ECMAScript3.Syntax

varDecl :: VarDecl a -> Id a
varDecl (VarDecl a x _ ) = x


forInit :: ForInit a -> [Id a]
forInit (VarInit decls) = map varDecl decls
forInit _ = []


forInInit :: ForInInit a -> [Id a]
forInInit (ForInVar x) = [x]
forInInit _ = []


caseClause :: CaseClause a -> [Id a]
caseClause (CaseClause _ e ss) = concatMap stmt ss
caseClause (CaseDefault _ ss) = concatMap stmt ss


catchClause :: CatchClause a -> [Id a]
catchClause (CatchClause _ x s) = stmt s


stmt :: Statement a -> [Id a]
stmt s = case s of
  VarDeclStmt _ decls -> map varDecl decls
  ForInStmt _ init _ s -> forInInit init ++ stmt s
  ForStmt _ init _ _ s -> forInit init ++ stmt s
  BlockStmt _ ss -> concatMap stmt ss
  EmptyStmt _ -> []
  ExprStmt _ _ -> []
  IfStmt _ _ s1 s2 -> stmt s1 ++ stmt s2
  IfSingleStmt _ _ s1 -> stmt s1
  SwitchStmt _ _ clauses -> concatMap caseClause clauses
  WhileStmt _ _ s -> stmt s
  DoWhileStmt _ s _ -> stmt s
  BreakStmt _ _ -> []
  ContinueStmt _ _ -> []
  LabelledStmt _ _ s -> stmt s
  TryStmt _ s catches finally -> 
    stmt s ++ maybe [] catchClause catches ++ maybe [] stmt finally
  ThrowStmt _ _ -> []
  ReturnStmt _ _ -> []
  WithStmt _ _ s -> stmt s
  FunctionStmt _ name _ _ -> [name]


localVars :: Statement a -> [String]
localVars = filter ((/=) "arguments") . map unId . stmt
