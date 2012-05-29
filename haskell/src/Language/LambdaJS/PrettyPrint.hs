module Language.LambdaJS.PrettyPrint
  ( pretty
  , op
  , renderExpr
  , opReps
  ) where


import Language.LambdaJS.Syntax
import Text.PrettyPrint.HughesPJ
import Control.Monad.State

opReps :: [(Op, String)]
opReps =
  [ (ONumPlus, "+"),
    (OStrPlus, "string-+"),
    (OMul, "*"),
    (ODiv, "/"),
    (OMod, "%"),
    (OSub, "-"),
    (OLt , "<"),
    (OStrLt, "string-<"),
    (OStrictEq, "==="),
    (OAbstractEq, "=="),
    (OTypeof, "typeof"),
    (OSurfaceTypeof, "surface-typeof"),
    (OPrimToNum, "prim->number"),
    (OPrimToStr, "prim->string"),
    (OPrimToBool, "prim->bool"),
    (OIsPrim, "prim?"),
    (OToInteger, "to-integer"),
    (OToInt32, "to-int-32"),
    (OToUInt32, "to-uint-32"),
    (OBAnd, "&"),
    (OBOr, "\\|"),
    (OBXOr, "^"),
    (OBNot, "~"),
    (OLShift, "<<"),
    (OSpRShift, ">>"),
    (OZfRShift, ">>>"),
    (OHasOwnProp, "has-own-prop?"),
    (OPrint, "print-string"),
    (OStrContains, "str-contains"),
    (OObjIterHasNext, "obj-iterate-has-next?"),
    (OObjIterNext, "obj-iterate-next"),
    (OObjIterKey, "obj-iterate-key"),
    (OStrStartsWith, "str-startswith"),
    (OStrLen, "str-length"),
    (OStrSplitRegExp, "str-split-regexp"),
    (OStrSplitStrExp, "str-split-strexp"),
    (OObjCanDelete, "obj-can-delete?"),
    (OMathExp, "math-exp"),
    (OMathLog, "math-log"),
    (OMathCos, "math-cos"),
    (OMathSin, "math-sin"),
    (OMathAbs, "math-abs"),
    (OMathPow, "math-pow"),
    (ORegExpQuote, "regexp-quote"),
    (ORegExpMatch, "regexp-match") ]

op :: Op -> Doc
op o = case lookup o opReps of
  Just s -> text s
  Nothing -> error "opReps is incomplete"

showNumber :: Double -> String
showNumber i 
 | isNaN i = "+nan.0"
 | isInfinite i = if (i > 0) then "+inf.0" else "-inf.0"
 | otherwise = show i


type M a = State Int a


newVar :: M Ident
newVar = do
  n <- get
  put (n + 1)
  return ("$" ++ show n)

--from http://bluebones.net/2007/01/replace-in-haskell/
replace :: Eq a => [a] -> [a] -> [a] -> [a]
replace [] _ _ = []
replace s find repl =
    if take (length find) s == find
        then repl ++ (replace (drop (length find) s) find repl)
        else [head s] ++ (replace (tail s) find repl)

conv :: String -> String
conv s = replace s "\\NUL" "\\0"

expr :: ExprPos -> M Doc
expr e = case e of
  ENumber a n -> return $ text (showNumber n)
  EString a s -> return $ text (conv $ show s) -- TODO: escaping from Haskell to Scheme?
  EBool a True -> return $ text "#t"
  EBool a False -> return $text "#f"
  EUndefined a -> return $ text "undefined"
  ENull a -> return $ text "null"
  ELambda a xs e -> do
    d <- expr e
    return $ parens $ text "lambda" <+> parens (hsep $ map text xs) $+$ d
  EObject a ps -> do
    let prop (x, e1) = do
          d1 <- expr e1
          return (parens (text (show x) <+> d1))
    props <- mapM prop ps
    return $ parens $ text "object" <+> vcat props
  EIf a e1 e2 e3 -> do
    d1 <- expr e1
    d2 <- expr e2
    d3 <- expr e3
    return $ parens $ text "if" <+> d1 $+$ d2 $+$ d3
  EId a x -> return (text x)
  EOp a o es -> do
    ds <- mapM expr es
    return $ parens $ op o <+> hsep ds
  EApp a e es -> do
    ds <- mapM expr (e:es)
    return $ parens $ hsep ds
  ELabel a lbl e -> do
    d <- expr e
    return $ parens $ text "label" <+> text lbl $+$ d
  EBreak a lbl e -> do
    d <- expr e
    return $ parens $ text "break" <+> text lbl $+$ d
  ESeq a e1 e2 -> do
    d1 <- expr e1
    d2 <- expr e2
    return $ parens $ text "begin" $+$ d1 $+$ d2
  ELet1 a bind1 eFn -> do
    v1 <- newVar
    d1 <- expr bind1
    d <- expr (eFn v1)
    return $ parens $ text "let" $+$ parens (parens $ text v1 $+$ d1) $+$ d
  ELet2 a bind1 bind2 eFn -> do
    v1 <- newVar
    v2 <- newVar
    d1 <- expr bind1
    d2 <- expr bind2
    d <- expr (eFn v1 v2)
    let binds = parens (text v1 $+$ d1) $+$ parens (text v2 $+$ d2)
    return $ parens $ text "let" $+$ parens binds $+$ d
  ELet a binds e -> do
    let f (x,e') = do
          d' <- expr e'
          return $ parens $ text x <+> d'
    dBinds <- mapM f binds
    d <- expr e
    return $ parens $ text "let" $+$ parens (vcat dBinds) $+$ d
  EThrow a e -> do
    d <- expr e
    return $ parens $ text "throw" <+> d
  ECatch a e1 e2 -> do
    d1 <- expr e1
    d2 <- expr e2
    return $ parens $ text "try-catch" $+$ d1 $+$ d2
  EFinally a e1 e2 -> do
    d1 <- expr e1
    d2 <- expr e2
    return $ parens $ text "try-finally" $+$ d1 $+$ d2
  ERef a e1 -> do
    d1 <- expr e1
    return $ parens $ text "alloc" <+> d1
  EDeref a e1 -> do
    d1 <- expr e1
    return $ parens $ text "deref" <+> d1
  EGetField a e1 e2 -> do
    d1 <- expr e1
    d2 <- expr e2
    return $ parens $ text "get-field" $+$ d1 $+$ d2
  ESetRef a e1 e2 -> do
    d1 <- expr e1
    d2 <- expr e2
    return $ parens $ text "set!" $+$ d1 $+$ d2
  EEval a -> return $ text "eval-semantic-bomb"
  EUpdateField a e1 e2 e3 -> do
    d1 <- expr e1
    d2 <- expr e2
    d3 <- expr e3
    return $ parens $ text "update-field" <+> d1 $+$ d2 $+$ d3
  EDeleteField a e1 e2 -> do
    d1 <- expr e1
    d2 <- expr e2
    return $ parens $ text "delete-field" <+> d1 $+$ d2
  EWhile a e1 e2 -> do
    d1 <- expr e1
    d2 <- expr e2
    return $ parens $ text "while" $+$ d1 $+$ d2

exprPositions :: ExprPos -> M Doc
exprPositions e = do
  inner <- expr e
  return $ parens $ text (show (exprLabel e)) $+$ inner

pretty :: ExprPos -> String
pretty e = render (renderExpr e)

renderExpr :: ExprPos -> Doc
renderExpr e = evalState (expr e) 0
