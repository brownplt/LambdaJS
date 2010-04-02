module BrownPLT.JavaScript.Analysis.AlphaRename ( alphaRename ) where

import Control.Monad.State
import BrownPLT.JavaScript.Semantics.Syntax
import BrownPLT.JavaScript.Semantics.RemoveHOAS

import qualified Data.Map as M

type Env = M.Map Ident Ident
type ENV = State (M.Map Ident Int)

nextVar :: Ident -> ENV Ident
nextVar s = do
  m <- get
  case M.lookup s m of
    Just d -> do
              let m' = M.insert s (d + 1) m
              put m'
              return (s ++ show (d + 1))
    Nothing -> do
              let m' =  M.insert s 0 m
              put m'
              return (s ++ show 0)

alphaRename' :: Env -> Expr a -> ENV (Expr a)
alphaRename' env e =
    case e of
      EId a x -> 
          case M.lookup x env of
            Just y -> return (EId a y)
            Nothing -> return e--fail ("Unbound id: " ++ (show x))
      ELambda a args body -> do
             newVars <- mapM nextVar args
             let env' = M.union (M.fromList (zip args newVars)) env
             body' <- alphaRename' env' body 
             return $ ELambda a newVars body'
      ELet a binds body ->
          let (names, values) = unzip binds
          in do
            newVars <- mapM nextVar names
            let env' = M.union (M.fromList (zip names newVars)) env
            values' <- mapM (alphaRename' env) values
            body' <- alphaRename' env' body
            return $ ELet a (zip newVars values') body'
      EObject a decls ->
          let (names, fields) = unzip decls
          in do
            fields' <- mapM (alphaRename' env) fields
            return $ EObject a (zip names fields')
      EOp a op args -> do
             args' <- mapM (alphaRename' env) args
             return $ EOp a op args'
      EApp a fun args -> do
             fun' <- alphaRename' env fun
             args' <- mapM (alphaRename' env) args
             return $ EApp a fun' args'
      ESetRef a x val -> do
             val' <- alphaRename' env val
             case M.lookup x env of
               Just y -> return $ ESetRef a y val'
               Nothing -> fail ("Unbound id: " ++ x)
      ERef a val -> do
             val' <- alphaRename' env val
             return $ ERef a val'
      EDeref a val -> do
             val' <- alphaRename' env val
             return $ EDeref a val'
      EGetField a obj name -> do
             obj' <- alphaRename' env obj
             name' <- alphaRename' env name
             return $ EGetField a obj' name'
      EDeleteField a obj name -> do
             obj' <- alphaRename' env obj
             name' <- alphaRename' env name
             return $ EDeleteField a obj' name'
      EUpdateField a obj name val -> do
             obj' <- alphaRename' env obj
             name' <- alphaRename' env name
             val' <- alphaRename' env val
             return $ EUpdateField a obj' name' val'
      ESeq a e1 e2 -> do
             e1' <- alphaRename' env e1
             e2' <- alphaRename' env e2
             return $ ESeq a e1' e2'
      EIf a c t e -> do
             c' <- alphaRename' env c
             t' <- alphaRename' env t
             e' <- alphaRename' env e
             return $ EIf a c' t' e'
      EWhile a test body -> do
             test' <- alphaRename' env test
             body' <- alphaRename' env body
             return $ EWhile a test' body'
      ELabel a lbl e -> do
             e' <- alphaRename' env e
             return $ ELabel a lbl e'
      EBreak a lbl e -> do
             e' <- alphaRename' env e
             return $ EBreak a lbl e'
      EThrow a e -> do
             e' <- alphaRename' env e
             return $ EThrow a e'
      ECatch a body catch -> do
             body' <- alphaRename' env body
             catch' <- alphaRename' env catch
             return $ ECatch a body' catch'
      EFinally a body catch -> do
             body' <- alphaRename' env body
             catch' <- alphaRename' env catch
             return $ EFinally a body' catch'
      ELet1 a _ _ -> fail ("Call removeHOAS first")
      ELet2 a _ _ _ -> fail ("Call removeHOAS first")
      otherwise -> return e


alphaRename :: Expr a -> Expr a
alphaRename e = evalState (alphaRename' M.empty (removeHOAS e)) M.empty
