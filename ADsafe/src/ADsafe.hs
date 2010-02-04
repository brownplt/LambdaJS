module Main ( main ) where

import Data.Map ( Map )
import qualified Data.Map as M

import System.Console.GetOpt
import System.Environment
import System.Exit

import BrownPLT.JavaScript.ADsafe.Transformation
import BrownPLT.JavaScript.ADsafe.DisableBanned
import BrownPLT.JavaScript.ADsafe.DisableEval
import BrownPLT.JavaScript.ADsafe.SimplifyIf
import BrownPLT.JavaScript.Parser ( parseScriptFromString )
import BrownPLT.JavaScript.Semantics.Desugar ( desugar )
import BrownPLT.JavaScript.Semantics.ECMAEnvironment ( ecma262Env )
import BrownPLT.JavaScript.Semantics.PrettyPrint ( pretty, prettyANF )
import BrownPLT.JavaScript.Semantics.Syntax
import BrownPLT.JavaScript.Semantics.ANF


desugarMain opts = do
  let env = case opts of 
              []        -> ecma262Env
              [NoEnv]   -> id
              otherwise -> fail "spurious command-line arguments"
  str <- getContents
  case parseScriptFromString "<stdin>" str of
    Right script -> 
      let core = adsafeDesugar script env
        in do putStrLn (pretty core)
              exitSuccess
    Left err -> do
      putStrLn (show err)
      exitFailure

desugarANF opts = do
  env <- return $ case opts of 
                    [] -> ecma262Env
                    [NoEnv] -> id
                    otherwise -> fail "spurious command line args"
  str <- getContents
  case parseScriptFromString "<stdin>" str of
    Right script -> do
      putStrLn (prettyANF (ifReduce (exprToANF (desugar script env))))
      exitSuccess
    Left err -> do
      putStrLn (show err)
      exitFailure


adsafeDesugar script env =
  let core1 = desugar script env
      core2 = flattenSeqs core1
      core3 = rewriteErrors core2
    in core3

typeCheckMain opts = do
  str <- getContents
  case parseScriptFromString "<stdin>" str of
    Right script -> do
      let core = adsafeDesugar script id
        in do
          putStrLn $ show $ isEvalTypeable (exprToANF core)
    Left err -> do
      putStrLn (show err)
      exitFailure

data Flag
  = Action ([Flag] -> IO ())
  | NoEnv

options :: [OptDescr Flag]
options =
  [ Option [] ["desugar"] (NoArg (Action desugarMain)) "desugar JavaScript"
  , Option [] ["anf"] (NoArg (Action desugarANF)) "desugar JavaScript"
  , Option [] ["no-env"] (NoArg NoEnv) "exclude standard environment"
  , Option [] ["type-check"] (NoArg (Action typeCheckMain)) "typecheck ADsafe code"
  ]

main :: IO ()
main = do
  args <- getArgs
  case getOpt RequireOrder options args of
    ((Action action):opts, [], []) -> action opts
    otherwise -> do
      putStrLn "Invalid command-line arguments"
      exitFailure
