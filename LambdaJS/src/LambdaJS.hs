module Main where

import LambdaJS.Parser (parseBinds)
import System.Console.GetOpt
import System.Environment
import System.Exit
import BrownPLT.JavaScript.Syntax (JavaScript (..))
import BrownPLT.JavaScript.Parser (parseScriptFromString, parseBlockStmt, 
  parseExpression, parseJavaScriptFromFile)
import Text.ParserCombinators.Parsec
import BrownPLT.JavaScript.Lexer (reservedOp, whiteSpace)
import BrownPLT.JavaScript.Semantics.PrettyPrint
import BrownPLT.JavaScript.Semantics.Syntax
import BrownPLT.JavaScript.Semantics.Desugar
import BrownPLT.JavaScript.Semantics.ECMAEnvironment
import Text.PrettyPrint.HughesPJ


desugarMain opts = do
  (env, prelude) <- case opts of
                      [EnvFile envFileName, PreludeFile preludeFileName] -> do
                        f <- getEnvTransformer envFileName
                        prelude <- parseJavaScriptFromFile preludeFileName
                        return (\e -> f (ecma262Env e), prelude)
                      [NoEnv] -> return (id, [])
                      otherwise -> fail "spurious command-line arguments"
  str <- getContents
  case parseScriptFromString "<stdin>" str of
    Right (Script p script) -> do
      putStrLn (pretty (desugar (Script p (prelude ++ script)) env))
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
  let src = renderExpr (EString nopos $ show srcLoc)
  let lhs = desugarStmtsWithResult [testStmt] ecma262Env 
               (getValue (EGetField nopos (EDeref nopos $ EId nopos "$global") 
                                    (EString nopos "result")))
  let rhs = getValue $ desugarExpr expectedExpr ecma262Env
  return $ parens (src <+> renderExpr lhs <+> renderExpr rhs)


testCases :: CharParser st Doc
testCases = do
  whiteSpace
  tests <- many testCase
  eof
  return $ parens (vcat tests)

getEnvTransformer fileName = do
  src <- readFile fileName
  case parseBinds fileName src of
    Left err -> fail (show err)
    Right f -> return f

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
  | EnvFile String
  | PreludeFile String

options :: [OptDescr Flag]
options =
  [ Option [] ["desugar"] (NoArg (Action desugarMain)) "desugar JavaScript"
  , Option [] ["test-cases"] (NoArg (Action testCaseMain)) "desugar test cases"
  , Option [] ["env"] (ReqArg EnvFile "FILENAME") "parse environment"
  , Option [] ["prelude"] (ReqArg PreludeFile "FILENAME") "JavaScript prelude"
  , Option [] ["no-env"] (NoArg NoEnv) "exclude standard environment"
  ]


main = do
  args <- getArgs
  case getOpt RequireOrder options args of
    ((Action action):opts, [], []) -> action opts
    otherwise -> do
      putStrLn "Invalid command line arguments"
      exitFailure
