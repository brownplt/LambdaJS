module Main ( main ) where

import Data.Map ( Map )
import qualified Data.Map as M
import Data.Char ( toLower )

import System.Console.GetOpt
import System.Environment
import System.Exit

import BrownPLT.JavaScript.ADsafe.Transformation
import qualified BrownPLT.JavaScript.ADsafe.DisableBanned as B
import qualified BrownPLT.JavaScript.ADsafe.DisableEval as E
import qualified BrownPLT.JavaScript.ADsafe.DisableWindow as W
import BrownPLT.JavaScript.ADsafe.SimplifyIf
import BrownPLT.JavaScript.Parser ( parseScriptFromString )
import BrownPLT.JavaScript.Semantics.Desugar ( desugar )
import BrownPLT.JavaScript.Semantics.ECMAEnvironment ( ecma262Env )
import BrownPLT.JavaScript.Semantics.PrettyPrint ( pretty, prettyANF )
import BrownPLT.JavaScript.Semantics.Syntax
import BrownPLT.JavaScript.Semantics.ANF
import BrownPLT.JavaScript.Semantics.RemoveHOAS


desugarMain     opts = mainTemplate pretty opts
desugarANFMain  opts = mainTemplate (prettyANF . adsafeANF) opts
getCheckMain    opts = mainTemplateShow  B.isTypeable opts
evalCheckMain   opts = mainTemplateShow  (E.isTypeable . adsafeANF) opts
windowCheckMain opts = mainTemplateShow  (W.isTypeable . adsafeANF) opts

mainTemplate :: (ExprPos -> String) -> [Flag] -> IO ()
mainTemplate fn opts = do
  str <- getContents
  case parseScriptFromString "<stdin>" str of
    Right script -> 
      let env = envForDesugar opts 
        in do putStrLn $ liftJS fn env script
              exitSuccess
    Left err -> do
      putStrLn $ show err
      exitFailure

mainTemplateShow :: Show a => (ExprPos -> a) -> [Flag] -> IO ()
mainTemplateShow f = mainTemplate (show . f)

liftJS fn env script = fn $ adsafeDesugar script env

adsafeDesugar script env =
  let core1 = desugar script env
      core2 = removeHOAS core1
      core3 = flattenSeqs core2
      core4 = rewriteErrors core3
    in core4

adsafeANF = ifReduce . exprToANF

envForDesugar :: [Flag] -> ExprPos -> ExprPos
envForDesugar opts | null [() | NoEnv <- opts] = id
                   | otherwise                 = ecma262Env

data Flag
  = Action ([Flag] -> IO ())
  | TypeCheck ([Flag] -> IO ())
  | NoEnv

data Checkers
  = Get
  | Eval
  | Window

readChecker = Action . readChecker' . (map toLower)
  where readChecker' "get"    = getCheckMain
        readChecker' "eval"   = evalCheckMain
        readChecker' "window" = windowCheckMain
        readChecker' _        = undefined

options :: [OptDescr Flag]
options =
  [ Option [] ["desugar"]      (NoArg (Action desugarMain))    "desugar JavaScript"
  , Option [] ["anf"]          (NoArg (Action desugarANFMain)) "desugar JavaScript into A-normal form"
  , Option [] ["no-env"]       (NoArg NoEnv)                   "exclude standard environment"
  , Option [] ["type-check"]   (ReqArg readChecker "CHECKER")  "run a type checker"
  ]

main :: IO ()
main = do
    args <- getArgs
    case getOpt RequireOrder options args of
      ((Action action):opts, [], []) -> action opts
      (_, _, errs) -> do
        putStrLn (concat errs ++ usageInfo header options)
        exitFailure
  where header = "Usage: adsafe [OPTION...]"

