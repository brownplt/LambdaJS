module Main ( main ) where

import System.Console.GetOpt
import System.Environment
import System.Exit

import BrownPLT.JavaScript.ADsafe.Transformation
import BrownPLT.JavaScript.Parser ( parseScriptFromString )
import BrownPLT.JavaScript.Semantics.Desugar ( desugar )
import BrownPLT.JavaScript.Semantics.ECMAEnvironment ( ecma262Env )
import BrownPLT.JavaScript.Semantics.PrettyPrint ( pretty )



desugarMain opts = do
  let env = case opts of 
              []        -> ecma262Env
              [NoEnv]   -> id
              otherwise -> fail "spurious command-line arguments"
  str <- getContents
  case parseScriptFromString "<stdin>" str of
    Right script -> do
      let core1 = desugar script env
          core2 = flattenSeqs core1
          core3 = rewriteErrors core2
      putStrLn (pretty core3)
      exitSuccess
    Left err -> do
      putStrLn (show err)
      exitFailure

data Flag
  = Action ([Flag] -> IO ())
  | NoEnv

options :: [OptDescr Flag]
options =
  [ Option [] ["desugar"] (NoArg (Action desugarMain)) "desugar JavaScript"
  , Option [] ["no-env"] (NoArg NoEnv) "exclude standard environment"
  ]

main :: IO ()
main = do
  args <- getArgs
  case getOpt RequireOrder options args of
    ((Action action):opts, [], []) -> action opts
    otherwise -> do
      putStrLn "Invalid command-line arguments"
      exitFailure
