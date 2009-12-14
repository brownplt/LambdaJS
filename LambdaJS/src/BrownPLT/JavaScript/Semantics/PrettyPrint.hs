module BrownPLT.JavaScript.Semantics.PrettyPrint
  ( pretty
  , renderExpr
  ) where


import BrownPLT.JavaScript.Semantics.Syntax
import Text.PrettyPrint.HughesPJ
import Control.Monad.State


op :: Op -> Doc
op o = text $ case o of
  ONumPlus -> "+"
  OStrPlus -> "string-+"
  OMul -> "*"
  ODiv -> "/"
  OMod -> "%"
  OSub -> "-"
  OLt  -> "<"
  OStrLt -> "string-<"
  OStrictEq -> "==="
  OAbstractEq -> "=="
  OTypeof -> "typeof"
  OSurfaceTypeof -> "surface-typeof"
  OPrimToNum -> "prim->number"
  OPrimToStr -> "prim->string"
  OPrimToBool -> "prim->bool"
  OIsPrim -> "prim?"
  OToInteger -> "to-integer"
  OToInt32 -> "to-int-32"
  OToUInt32 -> "to-uint-32"
  OBAnd -> "&"
  OBOr -> "\\|"
  OBXOr -> "^"
  OBNot -> "~"
  OLShift -> "<<"
  OSpRShift -> ">>"
  OZfRShift -> ">>>"
  OHasOwnProp -> "has-own-prop?"
  OPrint -> "print-string"
  OStrContains -> "str-contains"
  OObjIterHasNext -> "obj-iterate-has-next?"
  OObjIterNext -> "obj-iterate-next"
  OObjIterKey -> "obj-iterate-key"
  OStrStartsWith -> "str-startswith"
  OStrLen -> "str-length"
  OStrSplitRegExp -> "str-split-regexp"
  OStrSplitStrExp -> "str-split-strexp"
  OObjCanDelete -> "obj-can-delete?"
  OMathExp -> "math-exp"
  OMathLog -> "math-log"
  OMathCos -> "math-cos"
  OMathSin -> "math-sin"
  OMathAbs -> "math-abs"
  OMathPow -> "math-pow"
  ORegExpQuote -> "regexp-quote"
  ORegExpMatch -> "regexp-match"


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

expr :: Expr -> M Doc
expr e = case e of
  ENumber n -> return $ text (showNumber n)
  EString s -> return $ text (conv $ show s) -- TODO: escaping from Haskell to Scheme?
  EBool True -> return $ text "#t"
  EBool False -> return $text "#f"
  EUndefined -> return $ text "undefined"
  ENull -> return $ text "null"
  ELambda xs e -> do
    d <- expr e
    return $ parens $ text "lambda" <+> parens (hsep $ map text xs) $+$ d
  EObject ps -> do
    let prop (x, e1) = do
          d1 <- expr e1
          return (parens (text (show x) <+> d1))
    props <- mapM prop ps
    return $ parens $ text "object" <+> vcat props
  EIf e1 e2 e3 -> do
    d1 <- expr e1
    d2 <- expr e2
    d3 <- expr e3
    return $ parens $ text "if" <+> d1 $+$ d2 $+$ d3
  EId x -> return (text x)
  EOp o es -> do
    ds <- mapM expr es
    return $ parens $ op o <+> hsep ds
  EApp e es -> do
    ds <- mapM expr (e:es)
    return $ parens $ hsep ds
  ELabel lbl e -> do
    d <- expr e
    return $ parens $ text "label" <+> text lbl $+$ d
  EBreak lbl e -> do
    d <- expr e
    return $ parens $ text "break" <+> text lbl $+$ d
  ESeq e1 e2 -> do
    d1 <- expr e1
    d2 <- expr e2
    return $ parens $ text "begin" $+$ d1 $+$ d2
  ELet1 bind1 eFn -> do
    v1 <- newVar
    d1 <- expr bind1
    d <- expr (eFn v1)
    return $ parens $ text "let" $+$ parens (parens $ text v1 $+$ d1) $+$ d
  ELet2 bind1 bind2 eFn -> do
    v1 <- newVar
    v2 <- newVar
    d1 <- expr bind1
    d2 <- expr bind2
    d <- expr (eFn v1 v2)
    let binds = parens (text v1 $+$ d1) $+$ parens (text v2 $+$ d2)
    return $ parens $ text "let" $+$ parens binds $+$ d
  ELet binds e -> do
    let f (x,e') = do
          d' <- expr e'
          return $ parens $ text x <+> d'
    dBinds <- mapM f binds
    d <- expr e
    return $ parens $ text "let" $+$ parens (vcat dBinds) $+$ d
  EThrow e -> do
    d <- expr e
    return $ parens $ text "throw" <+> d
  ECatch e1 e2 -> do
    d1 <- expr e1
    d2 <- expr e2
    return $ parens $ text "try-catch" $+$ d1 $+$ d2
  EFinally e1 e2 -> do
    d1 <- expr e1
    d2 <- expr e2
    return $ parens $ text "try-finally" $+$ d1 $+$ d2
  ERef e1 -> do
    d1 <- expr e1
    return $ parens $ text "alloc" <+> d1
  EDeref e1 -> do
    d1 <- expr e1
    return $ parens $ text "deref" <+> d1
  EGetField e1 e2 -> do
    d1 <- expr e1
    d2 <- expr e2
    return $ parens $ text "get-field" $+$ d1 $+$ d2
  ESetRef e1 e2 -> do
    d1 <- expr e1
    d2 <- expr e2
    return $ parens $ text "set!" $+$ d1 $+$ d2
  EEval -> return $ text "eval-semantic-bomb"
  EUpdateField e1 e2 e3 -> do
    d1 <- expr e1
    d2 <- expr e2
    d3 <- expr e3
    return $ parens $ text "update-field" <+> d1 $+$ d2 $+$ d3
  EDeleteField e1 e2 -> do
    d1 <- expr e1
    d2 <- expr e2
    return $ parens $ text "delete-field" <+> d1 $+$ d2
  EWhile e1 e2 -> do
    d1 <- expr e1
    d2 <- expr e2
    return $ parens $ text "while" $+$ d1 $+$ d2


pretty :: Expr -> String
pretty e = render (renderExpr e)

renderExpr :: Expr -> Doc
renderExpr e = evalState (expr e) 0
