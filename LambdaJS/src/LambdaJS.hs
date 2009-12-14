module Main where

import System.Console.GetOpt
import System.Environment
import System.Exit
import BrownPLT.JavaScript.Parser (parseScriptFromString, parseBlockStmt, 
  parseExpression)
import Text.ParserCombinators.Parsec
import BrownPLT.JavaScript.Lexer (reservedOp, whiteSpace)
import BrownPLT.JavaScript.Semantics.PrettyPrint
import BrownPLT.JavaScript.Semantics.Syntax
import BrownPLT.JavaScript.Semantics.Desugar
import BrownPLT.JavaScript.Semantics.ECMAEnvironment
import Text.PrettyPrint.HughesPJ


desugarMain opts = do
  env <- return $ case opts of
           [] -> ecma262Env
           [NoEnv] -> id
           otherwise -> fail "spurious command-line arguments"
  str <- getContents
  case parseScriptFromString "<stdin>" str of
    Right script -> do
      putStrLn (pretty (desugar script env))
      exitSuccess
    Left err -> do
      putStrLn (show err)
      exitFailure


testCase :: CharParser st Doc
testCase = do
  srcLoc <- getPosition
  testStmt <- parseBlockStmt
  reservedOp "::"
  expectedExpr <- parseExpression
  reservedOp ";"
  let src = renderExpr (EString $ show srcLoc)
  let lhs = desugarStmtsWithResult [testStmt] ecma262Env 
               (getValue (EGetField (EDeref $ EId "$global") 
                                    (EString "result")))
  let rhs = getValue $ desugarExpr expectedExpr ecma262Env
  return $ parens (src <+> renderExpr lhs <+> renderExpr rhs)


testCases :: CharParser st Doc
testCases = do
  whiteSpace
  tests <- many testCase
  eof
  return $ parens (vcat tests)


testCaseMain [] = do
  src <- getContents
  case parse testCases "stdin" src of
    Left err -> putStrLn (show err)
    Right tests -> putStrLn (render tests)
testCaseMain _ =
  fail "spurious command-line arguments"


data Flag
  = Action ([Flag] -> IO ())
  | NoEnv

options :: [OptDescr Flag]
options =
  [ Option [] ["desugar"] (NoArg (Action desugarMain)) "desugar JavaScript"
  , Option [] ["test-cases"] (NoArg (Action testCaseMain)) "desugar test cases"
  , Option [] ["no-env"] (NoArg NoEnv) "exclude standard environment"
  ]


main = do
  args <- getArgs
  case getOpt RequireOrder options args of
    ((Action action):opts, [], []) -> action opts
    otherwise -> do
      putStrLn "Invalid command line arguments"
      exitFailure