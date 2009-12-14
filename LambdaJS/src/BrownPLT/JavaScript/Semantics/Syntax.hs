module BrownPLT.JavaScript.Semantics.Syntax
  ( Ident
  , Label
  , Op(..)
  , Expr(..)
  ) where 

type Ident = String
type Label = String

data Op
  = ONumPlus
  | OStrPlus
  | OMul | ODiv | OMod | OSub
  | OLt  | OStrLt
  | OBAnd | OBOr | OBXOr | OBNot
  | OLShift | OSpRShift | OZfRShift
  | OStrictEq
  | OAbstractEq
  | OTypeof
  | OSurfaceTypeof
  | OPrimToNum
  | OPrimToStr
  | OPrimToBool
  | OIsPrim
  | OHasOwnProp
  | OToInteger | OToInt32 | OToUInt32
  | OPrint -- ^for Rhino
  | OStrContains | OStrSplitRegExp | OStrSplitStrExp -- ^for Regexes
  | OStrStartsWith -- ^for forin
  | OStrLen
  | OObjIterHasNext | OObjIterNext | OObjIterKey -- ^more forin
  | OObjCanDelete
  | OMathExp | OMathLog | OMathCos | OMathSin | OMathAbs | OMathPow
  | ORegExpMatch | ORegExpQuote
  deriving (Eq, Show)

data Expr
  = ENumber Double
  | EString String
  | EBool Bool
  | EUndefined
  | ENull
  | ELambda [Ident] Expr
  | EObject [(String, Expr)]
  | EId Ident
  | EOp Op [Expr]
  | EApp Expr [Expr]
  | ELet [(Ident, Expr)] Expr
  | ESetRef Expr Expr
  | ERef Expr
  | EDeref Expr
  | EGetField Expr Expr
  | EUpdateField Expr Expr Expr
  | EDeleteField Expr Expr
  | ESeq Expr Expr
  | EIf Expr Expr Expr
  | EWhile Expr Expr
  | ELabel Label Expr
  | EBreak Label Expr
  | EThrow Expr
  | ECatch Expr Expr
  | EFinally Expr Expr
  -- |We use HOAS when possible so that we don't mess up bindings.  When
  -- pretty-printing, we unravel these to use conventional bindings.
  | ELet1 Expr (Ident -> Expr) 
  | ELet2 Expr Expr (Ident -> Ident -> Expr)
  | EEval -- ^an expression that calls eval, or a related function.  If
          -- EEval becomes the active expression, our model immediately aborts.
