module Main ( main ) where

import Data.Char ( toLower )
import Data.Either ( either )
import Data.Map ( Map )
import qualified Data.Map as M

import System.Console.GetOpt
import System.Environment
import System.Exit

import BrownPLT.JavaScript.ADsafe.Transformation
import qualified BrownPLT.JavaScript.ADsafe.DisableBanned as B
import qualified BrownPLT.JavaScript.ADsafe.DisableEval as E
import qualified BrownPLT.JavaScript.ADsafe.DisableWindow as W
import qualified BrownPLT.JavaScript.ADsafe.MakeableTags as K
import BrownPLT.JavaScript.ADsafe.SimplifyIf
import BrownPLT.JavaScript.Parser ( parseScriptFromString )
import BrownPLT.JavaScript.Semantics.Desugar ( desugar )
import BrownPLT.JavaScript.Semantics.ECMAEnvironment ( ecma262Env )
import BrownPLT.JavaScript.Semantics.PrettyPrint ( pretty, prettyANF )
import BrownPLT.JavaScript.Semantics.Syntax
import BrownPLT.JavaScript.Semantics.ANF
import BrownPLT.JavaScript.Semantics.RemoveHOAS
import BrownPLT.JavaScript.Semantics.Parser as P
import BrownPLT.JavaScript.Analysis.RemoveUnused
import BrownPLT.JavaScript.Analysis.PushDown
import BrownPLT.JavaScript.Analysis.MergeSequences
import BrownPLT.JavaScript.Analysis.AlphaRename

desugarMain     opts = mainTemplate pretty opts
desugarANFMain  opts = mainTemplate (prettyANF . adsafeANF) opts
getCheckMain    opts = mainTemplateError B.isTypeable opts
evalCheckMain   opts = mainTemplateError E.isTypeable opts
windowCheckMain opts = mainTemplateError (W.isTypeable . checkANF) opts
tagCheckMain    opts = mainTemplateError (K.isTypeable . checkANF) opts

mainTemplate :: (ExprPos -> String) -> [Flag] -> IO ()
mainTemplate fn opts = 
    case opts of
      opts | null [() | LJS <- opts] -> do
                str <- getContents
                case parseScriptFromString "<stdin>" str of
                  Right script -> 
                      let env = envForDesugar opts 
                      in do putStrLn $ liftJS fn env script
                            exitSuccess
                  Left err -> do
                    putStrLn $ show err
                    exitFailure
      otherwise -> do
                str <- getContents
                case P.parseExprFromString "<stdin>" str of
                  Right script -> 
                      do putStrLn $ fn script
                         exitSuccess
                  Left err -> do
                     putStrLn $ show err
                     exitFailure
                
mainTemplateShow :: Show a => (ExprPos -> a) -> [Flag] -> IO ()
mainTemplateShow f = mainTemplate (show . f)

mainTemplateError :: Show a => (ExprPos -> Either String a) -> [Flag] -> IO ()
mainTemplateError f = mainTemplate ((either id show) . f)

liftJS fn env script = fn $ adsafeDesugar script env

adsafeDesugar script env =
  let core1 = desugar script env
      core2 = removeHOAS core1
      core3 = flattenSeqs core2
      core4 = rewriteErrors core3
      core5 = alphaRename core4
    in core5

adsafeANF = mergeSeqs . pushDown . removeUnused . ifReduce . removeUnused .  ifReduce . (exprToANF "$anf")
checkANF = (exprToANF "$$anf")

envForDesugar :: [Flag] -> ExprPos -> ExprPos
envForDesugar opts | null [() | NoEnv <- opts] = ecma262Env
                   | otherwise                 = id

data Flag
  = Action ([Flag] -> IO ())
  | TypeCheck ([Flag] -> IO ())
  | LJS
  | NoEnv

data Checkers
  = Get
  | Eval
  | Window
  | Tags

readChecker = Action . readChecker' . (map toLower)
  where readChecker' "get"    = getCheckMain
        readChecker' "eval"   = evalCheckMain
        readChecker' "window" = windowCheckMain
        readChecker' "tags"   = tagCheckMain
        readChecker' _        = undefined

options :: [OptDescr Flag]
options =
  [ Option [] ["desugar"]      (NoArg (Action desugarMain))    "desugar JavaScript"
  , Option [] ["anf"]          (NoArg (Action desugarANFMain)) "desugar JavaScript into A-normal form"
  , Option [] ["no-env"]       (NoArg NoEnv)                   "exclude standard environment"
  , Option [] ["type-check"]   (ReqArg readChecker "CHECKER")  "run a type checker"
  , Option [] ["ljs"]          (NoArg LJS)                     "parse lambda-js syntax"
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

