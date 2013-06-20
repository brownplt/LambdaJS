-- |Lifts function statements to the enclosing block, and turn them into
-- function expressions.
module Language.LambdaJS.LiftFuncStmts
  ( liftFuncStmts
  ) where

import Language.LambdaJS.Prelude
import Language.ECMAScript3
import Data.Generics

isFuncExpr :: Expression SourcePos -> Bool
isFuncExpr (FuncExpr{}) = True
isFuncExpr _ = False


isFuncStmt :: Statement SourcePos -> Bool
isFuncStmt (FunctionStmt{}) = True
isFuncStmt _ = False


isNewScope :: Data a => a -> Bool
isNewScope = mkQ False (isFuncExpr `extQ` isFuncStmt)


collectFuncStmts :: Data a
                 => a
                 -> [Statement SourcePos]
collectFuncStmts = collectExclude (not.isNewScope) isFuncStmt


removeFuncStmts :: Data a => a -> a
removeFuncStmts = everywhereUpto isNewScope (mkT toEmptyStmt)
  where toEmptyStmt :: Statement SourcePos -> Statement SourcePos
        toEmptyStmt (FunctionStmt p _ _ _) = EmptyStmt p
        toEmptyStmt s = s


funcStmtToVarDecl :: Statement SourcePos
                  -> Statement SourcePos
funcStmtToVarDecl (FunctionStmt p x args body) = 
  VarDeclStmt p [VarDecl p x (Just expr)]
    where expr = FuncExpr p Nothing args body
funcStmtToVarDecl s = 
  error $ "LiftFuncStmts.hs : expected FunctionStmt, got " ++ show s

liftFuncStmts :: [Statement SourcePos]
              -> [Statement SourcePos]
liftFuncStmts stmts = varDecls ++ stmts'
  where stmts' = removeFuncStmts stmts
        varDecls = map funcStmtToVarDecl (collectFuncStmts stmts)
