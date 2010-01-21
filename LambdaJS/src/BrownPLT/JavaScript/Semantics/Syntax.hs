module BrownPLT.JavaScript.Semantics.Syntax
  ( Ident
  , Label
  , Op(..)
  , Expr(..)
  , ExprPos
  , exprLabel
  , label
  , label'
  , SourcePos
  , nopos
  ) where 


import Control.Applicative ( Alternative(..) )
import Control.Arrow ( second , (***) )
import Data.Maybe ( fromMaybe, fromJust )
import Data.Map (Map,(!))
import Data.Generics

import BrownPLT.JavaScript.Semantics.Prelude

import Text.ParserCombinators.Parsec(SourcePos) -- used by data JavaScript
import Text.ParserCombinators.Parsec.Pos(newPos) -- used by data JavaScript

type Ident = String
type Label = String

type ExprPos = Expr SourcePos

nopos = newPos "nothing" 0 0

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
  deriving (Eq, Show, Data, Typeable, Ord)

data Expr a
  = ENumber a Double
  | EString a String
  | EBool a Bool
  | EUndefined a
  | ENull a
  | ELambda a [Ident] (Expr a)
  | EObject a [(String, (Expr a))]
  | EId a Ident
  | EOp a Op [Expr a]
  | EApp a (Expr a) [Expr a]
  | ELet a [(Ident, (Expr a))] (Expr a)
  | ESetRef a (Expr a) (Expr a)
  | ERef a (Expr a)
  | EDeref a (Expr a)
  | EGetField a (Expr a) (Expr a)
  | EUpdateField a (Expr a) (Expr a) (Expr a)
  | EDeleteField a (Expr a) (Expr a)
  | ESeq a (Expr a) (Expr a)
  | EIf a (Expr a) (Expr a) (Expr a)
  | EWhile a (Expr a) (Expr a)
  | ELabel a Label (Expr a)
  | EBreak a Label (Expr a)
  | EThrow a (Expr a)
  | ECatch a (Expr a) (Expr a)
  | EFinally a (Expr a) (Expr a)
  -- |We use HOAS when possible so that we don't mess up bindings.  When
  -- pretty-printing, we unravel these to use conventional bindings.
  | ELet1 a (Expr a) (Ident -> (Expr a))
  | ELet2 a (Expr a) (Expr a) (Ident -> Ident -> (Expr a))
  | EEval a -- ^an expression that calls eval, or a related function.  If
            -- EEval becomes the active expression, our model immediately aborts.
  deriving (Show, Data, Typeable)

instance Show a => Show (Ident -> Expr a) where
    show a = "test"

instance Show a => Show (Ident -> Ident -> Expr a) where
    show a = "test"

-- Generic function to retrieve the value of type 'a' from a data structure of
-- type 'c a', if it exists.
--
label' :: (Typeable a, Data (c a)) => c a -> Maybe a
label' = gmapQl (<|>) Nothing (Nothing `mkQ` (Just :: a -> Maybe a))


-- Generic function to retrieve the value of type 'a' from a data structure of
-- type 'c a'.
--
-- Note that in order for this to be safe, each variant of the data type 'c a' 
-- must include a value of type 'a' as an immediate child. In the ANF syntax,
-- the 'Lit' variant of the 'Expr' data type violates this assumption.
-- 
label :: (Typeable a, Data (c a)) => c a -> a
label = fromJust . label'

-- 'label' specialized to Expr
--
exprLabel :: Data a => Expr a -> a
exprLabel = label



