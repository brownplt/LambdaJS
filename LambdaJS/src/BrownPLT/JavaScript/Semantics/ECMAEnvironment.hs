module BrownPLT.JavaScript.Semantics.ECMAEnvironment
  ( ecma262Env
  ) where

import BrownPLT.JavaScript.Semantics.Desugar
import BrownPLT.JavaScript.Semantics.Syntax
import Text.ParserCombinators.Parsec
import BrownPLT.JavaScript.Parser (parseExpression)
import qualified Data.Map as M


object :: [(Ident, Expr)] -> Expr
object props = EObject $ map (\(x, e) -> (x, e)) props


-- |helper to have already bound IDs
lambda :: [Ident] -> Expr -> Expr
lambda args body = ELambda ["this", "arguments"] body'
  where body' = ELet (map arg (zip args [0..])) body
        arg (x,n) = (x,EGetField (EDeref (EDeref (EId "arguments")))
                                   (EString (show n)))
-- |Wraps the body of a lambda expression into a function object
functionObject :: [Ident] -> Expr -> Expr
functionObject args body = ERef $ object 
  [ ("$code", lambda args body)
  , ("arguments", ENull)
  , ("prototype", ERef $ object [("$proto", EId "$Object.prototype")])
--  , ("$class", EString "Function")
  , ("$proto", EId "$Function.prototype")
  , ("length", ENumber (fromIntegral $ length args))
  , ("$strRep", EString "function fromafunctionboject(){}")
  ]


--evaluates the 1st expr if the function was called as a constructor,
--and the 2nd if it was called as a function
splitConstr :: Expr -> Expr -> Expr
splitConstr eConstr eFunc = 
  EIf (eNot (isUndefined $ getFieldT (EString "$constructing")))
      eConstr
      eFunc
      


asVariables :: [(Ident, Expr)] -> [(Ident, Expr)]
asVariables binds = map (\(x, e) -> (x, ERef e)) binds


-- |Section 15.1
globalValuesAndFunctions :: [(Ident, Expr)] 
globalValuesAndFunctions = 
  [ ("$proto", EId "$Object.prototype")
  , ("$class", EString "global")
  , ("NaN", ENumber (0.0/0.0))
  , ("Infinity", ENumber (1.0/0.0))
  , ("undefined", EUndefined)
  -- TODO: parseInt and parseFloat are oversimplified
  , ("parseInt", functionObject ["n"] $ 
    EOp OPrimToNum [toString $ EId "n"])
  , ("parseFloat", functionObject ["n"] $ 
    EOp OPrimToNum [toString $ EId "n"])
  , ("isNaN", functionObject ["n"] $ 
       eStxEq (ENumber (0.0/0.0)) (toNumber (EId "n")))
  , ("isFinite", functionObject ["x"] $
     ELet [("n", toNumber (EId "x"))] $
       EIf (eStxEq (EId "n") (ENumber (0.0/0.0))) (EBool False) $
       EIf (eStxEq (EId "n") (ENumber (1.0/0.0))) (EBool False) $
       EIf (eStxEq (EId "n") (ENumber (-1.0/0.0))) (EBool False) $
       (EBool True))
  -- TODO: URI functions don't transform URLs correctly.  But, the type
  -- conversion is in place.
  , ("decodeURI", functionObject ["encodedURI"] $
     toString $ EId "decodeURI")
  , ("decodeURIComponent", functionObject ["encodedURIComponent"] $
      toString $ EId "encodedURIComponent")
  , ("encodeURI", functionObject ["uri"] $
      toString $ EId "uri")
  , ("encodeURIComponent", functionObject ["uriComponent"] $
      toString $ EId "uriComponent")
  , ("eval", functionObject [] EEval)
  --these are refs of refs, so we must deref:
  , ("Object", EDeref $ EId "Object")
  , ("Function", EDeref $ EId "Function")
  , ("Array", EDeref $ EId "Array")
  , ("RegExp", EDeref $ EId "RegExp")
  , ("String", EDeref $ EId "String")
  , ("Date", EDeref $ EId "Date")
  , ("Number", EDeref $ EId "Number")
  , ("Boolean", EDeref $ EId "Boolean")
  
  , ("Error", EDeref $ EId "Error")
  , ("ConversionError", EDeref $ EId "ConversionError")
  , ("EvalError", EDeref $ EId "EvalError")
  , ("RangeError", EDeref $ EId "RangeError")
  , ("ReferenceError", EDeref $ EId "ReferenceError")
  , ("SyntaxError", EDeref $ EId "SyntaxError")
  , ("TypeError", EDeref $ EId "TypeError")
  , ("URIError", EDeref $ EId "URIError")

  , ("print", functionObject ["V"] $ EOp OPrint [toString (EId "V")])
  , ("Math", ERef $ object $
    [ ("$class", EString "Math")
    , ("$proto", EId "$Object.prototype") 
    , ("E", ENumber (exp 1))
    , ("LN10", ENumber (log 10))
    , ("LN2", ENumber (log 2))
    , ("LOG2E", ENumber (log (exp 1) / log 2))
    , ("LOG10E", ENumber (log (exp 1) / log 10))
    , ("PI", ENumber pi)
    , ("SQRT1_2", ENumber (sqrt (1.0/2.0)))
    , ("SQRT2", ENumber (sqrt 2))

    , ("exp", mathFunc OMathExp)
    , ("log", mathFunc OMathLog)
    , ("sin", mathFunc OMathSin)
    , ("cos", mathFunc OMathCos)
    , ("abs", mathFunc OMathAbs)
    , ("pow", mathFunc2 OMathPow)
    ])  
  ]
 where
  mathFunc op = functionObject ["x"] (EOp op [toNumber (EId "x")])
  mathFunc2 op = functionObject ["x","y"] (EOp op [toNumber (EId "x"),
                                                   toNumber (EId "y")])

--update the object with everything in the given list
--used to close recursions
updateObject :: Expr -> [(Ident, Expr)] -> Expr -> Expr
updateObject objE [] rest = rest
updateObject objE ((name,e):xs) rest = 
  ESeq (setField objE (EString name) e)
       (updateObject objE xs rest)

--helper to ensure the corrakt type of 'this'
checkThis expected = EIf (eNot (eStxEq (getFieldT (EString "$class")) 
                                       (EString expected)))
                (EThrow $ newError "TypeError" $ 
                  "expected " ++ expected ++ " obj, got smth else")

-- |Sections 15.2.3 and 15.2.4
-- TODO : isPrototypeOf and propertyIsEnumerable
objectPrototypeValues =
  [ ("$proto", ENull)
  , ("$class", EString "Object")
  , ("constructor", EUndefined) -- Set to Object later
  , ("toString", functionObject [] $
       EOp OStrPlus [EString "[object ",
                     EOp OStrPlus [EGetField (EDeref $ EId "this") 
                                             (EString "$class"),
                                   EString "]"]])
  , ("toLocaleString", functionObject [] $
       EOp OStrPlus [EString "[object ",
                     EOp OStrPlus [EGetField (EDeref $ EId "this") 
                                             (EString "$class"),
                                   EString "]"]])
  , ("valueOf", functionObject [] $ EId "this")
  , ("hasOwnProperty", functionObject ["V"] $
       EOp OHasOwnProp [EDeref $ EId "this",
                        toString (EId "V")])
  ]

nativeFunctionStrRep name = "function "++name++"() {\n    [native code]\n}"
--various algorithms that are more easily expressed as js:  
parseSrc src = case parse parseExpression "<built-in>" src of
  Right x -> x
  Left y -> error $ "Error parsing built-in src: " ++ (show y)

--insertion sort since too lazy to qsort.
arraySort = parseSrc "(function (comparefn) { \n\
\  var l = this.length; \n\
\  var sortCompare = function(x,y) { \n\
\    if (x === undefined && y === undefined) return 0; \n\
\    if (x === undefined) return 1; \n\
\    if (y === undefined) return -1; \n\
\    if (comparefn === undefined) { \n\
\      var xs = \"\"+x; var ys = \"\"+y; \n\
\      if (xs < ys) return -1; \n\
\      if (ys < xs) return 1; \n\
\      return 0; \n\
\    } \n\
\    return comparefn(x,y); \n\
\  }; \n\
\  \n\
\  for (var i=0; i<l-1; i++) { \n\
\    //find the min and swarp it \n\
\    var min = i; \n\
\    for (var j=i+1; j<l; j++) { \n\
\      if (sortCompare(this[j],this[i]) < 0) min = j; \n\
\    }  \n\
\    var tmp = this[i]; \n\
\    this[i] = this[min]; \n\
\    this[min] = tmp; \n\
\  } \n\
\ })" 
arrayJoin = parseSrc "function (separator) {      \n\
\  var l = this.length;  \n\
\  if (separator === undefined) separator = \",\";   \n\
\  separator = \"\"+separator;  \n\
\  if (l === 0) return \"\";  \n\
\  var R = this[0];  \n\
\  if (R === undefined || R === null)  \n\
\    R = \"\";  \n\
\  else  \n\
\    R = \"\"+R;  \n\
\  for (var k = 1; k < l; ++k) {  \n\
\    var S = R + separator;  \n\
\    var x = this[k];  \n\
\    if (x === undefined || x === null) {  \n\
\      R = S + \"\";  \n\
\    }  \n\
\    else  \n\
\      R = S + (\"\"+x);  \n\
\  }  \n\
\  return R;  \n\
\ }"

arrayJoinLocale = parseSrc "function () {      \n\
\  var l = this.length;  \n\
\  var separator = \",\";   \n\
\  if (l === 0) return \"\";  \n\
\  var R = this[0];  \n\
\  if (R === undefined || R === null)  \n\
\    R = \"\";  \n\
\  else  \n\
\    R = R.toLocaleString();  \n\
\  for (var k = 1; k < l; ++k) {  \n\
\    var S = R + separator;  \n\
\    var x = this[k];  \n\
\    if (x === undefined || x === null) {  \n\
\      R = S + \"\";  \n\
\    }  \n\
\    else  \n\
\      R = S + (x.toLocaleString());  \n\
\  }  \n\
\  return R;  \n\
\ }"


-- |Section 15.4.4
arrayPrototype :: Expr
arrayPrototype = object
  [ ("$proto", EId "$Object.prototype")
  , ("$class", EString "Object")
  , ("length", ENumber 0)
  , ("constructor", EUndefined) -- Set to Array later
  , ("toString", functionObject [] $ checkThis "Array" $ 
      applyObj (EGetField (EDeref $ EId "this") (EString "join")) 
               (EId "this") [])
  , ("toLocaleString", desugarExprSetenv arrayJoinLocale 
                         (M.singleton "this" True))
  , ("concat", (EString "TODO: Array.prototype.concat"))
  , ("join", desugarExprSetenv arrayJoin (M.singleton "this" True))
  , ("pop", functionObject [] $
    (EIf (eStxEq (getFieldT (EString "length")) (ENumber 0))
         EUndefined $
         --set length to length-1, get the item there, delete it, and return
         ELet [("$newlen", (EOp ONumPlus 
           [primToNum (getFieldT (EString "length")), ENumber (-1)]))] $
           ELet [("$result", getFieldT (primToStr (EId "$newlen")))] $
             ESeq (setFieldT (EString "length") (EId "$newlen")) $
               ESeq (ESetRef (EId "this")
                      (EDeleteField (EDeref $ EId "this")
                                    (primToStr $ EId "$newlen")))
                    (EId "$result")))
  , ("push", functionObject [] $ --use a for loop:
    ELet [("$i", ERef (ENumber 0))] $ ESeq ( 
      eFor EUndefined --init, incr, test, body
           (ESetRef (EId "$i") (EOp ONumPlus [EDeref (EId "$i"), ENumber 1]))
           (EOp OLt [EDeref (EId "$i"),
                     EGetField (EDeref (EDeref (EId "arguments"))) 
                               (EString "length")])
           (ESeq (setFieldT (primToStr (getFieldT (EString "length")) )
                            (EGetField (EDeref (EDeref (EId "arguments")))
                                       (primToStr (EDeref $ EId "$i"))))
                 (setFieldT (EString "length")
                            (EOp ONumPlus [getFieldT (EString "length"),
                                          ENumber 1]))))
           (getFieldT (EString "length"))) --return the new length
  , ("reverse", (EString "TODO: Array.prototype.reverse"))
  , ("shift", (EString "TODO: Array.prototype.shift"))
  , ("slice", (EString "TODO: Array.prototype.slice"))
  , ("sort", desugarExprSetenv arraySort (M.singleton "this" True))
  , ("splice", (EString "TODO: Array.prototype.splice"))
  , ("unshift", (EString "TODO: Array.prototype.unshift"))
  ]
  
-- |Section 15.4.4
regExpPrototype :: Expr
regExpPrototype = object
  [ ("$proto", EId "$Object.prototype")
  , ("$class", EString "Object")
  , ("length", ENumber 0)
  , ("constructor", EUndefined) -- Set to RegExp later
  --, ("toString", (EString "TODO: regExp.prototype.toString"))
  --TODO: make this return an array with 'index' and 'input'
  , ("exec", functionObject ["$$string"] $ checkThis "RegExp" $ 
    EIf (eOr (getFieldT (EString "global"))
             (getFieldT (EString "ignoreCase")))
      (EThrow (EString "regexp not fully impl yet")) $
      ELet1 (toString $ EId "$$string") (\str -> 
        ELet1 (EOp ORegExpMatch [EId str, getFieldT (EString "$regexpPattern")])
          (\matchRes -> EIf (isUndefined (EId matchRes)) ENull $
            eNewDirect (EDeref $ EId "Array") (ERef $ ERef $ EId matchRes))))
  , ("test", EString "TODO: RegExp.prototype.test")
  ]


-- |Sections 15.2.1 and 15.2.2
jsObject :: Expr
jsObject = ERef $ object
  [ ("$proto", EId "$Function.prototype") -- Yes, this is correct.
  , ("prototype", EId "$Object.prototype")
  , ("length", ENumber 1)
  , ("$code", lambda ["value"] $ 
       EIf (EIf (EOp OStrictEq [EId "value", EUndefined])
                (EBool True)
                (EOp OStrictEq [EId "value", ENull]))
           (ERef $ object [ ("$class", EString "Object")
                          , ("$proto", EId "$Object.prototype")
                          ])
           (toObject (EId "value")))
  ]


--helpers for constructors:
setField lhse fnamee fe =
  ESetRef lhse (EUpdateField (EDeref lhse) fnamee fe)
setFieldT = setField (EId "this")
setFieldTS a b = ESeq $ setField (EId "this") a b
getField lhse fnamee = EGetField (EDeref lhse) fnamee
getFieldT = getField (EId "this")

-- |Section 15.4.2
-- TODO: make it work as a non-constr too
jsArray :: Expr
jsArray = ERef $ object
  [ ("$proto", EId "$Function.prototype")
  , ("length", ENumber 1)
  , ("prototype", EId "$Array.prototype")
  , ("$strRep", EString $ nativeFunctionStrRep "Array")
  --15.4.2.1
  , ("$code", constr)
  ]
 where
  constr = lambda ["$arg0"] $ 
    ELet [("$numArgs", EGetField (EDeref $ EDeref $ EId "arguments")
                                 (EString "length"))] $
      splitConstr asConstr asFunc
  asFunc = eNewDirect (getField (EId "$global") (EString "Array")) 
             (EId "arguments")
  asConstr = 
      --if there is 1 arg and it is a number, we do something else:
      EIf (eAnd (eStxEq (EId "$numArgs") (ENumber 1))
                (isNumber (EId "$arg0")))
          (EIf (eStxEq (EOp OToUInt32 [(EId "$arg0")])
                       (EId "$arg0"))
               (objsetup (EId "$arg0") EUndefined)
               (EThrow $ newError "RangeError" "invalid len to new Array()"))
          --otherwise we do this:
          (objsetup (EId "$numArgs") objconstr)
  objsetup lengthe r = 
    ESeq (setFieldT (EString "$class") (EString "Array"))
         (ESeq (setFieldT (EString "$proto") (EId "$Array.prototype"))
               (ESeq (setFieldT (EString "length") lengthe)
                     r))
  objconstr = 
    ELet [("$i", ERef $ ENumber 0)] $
      EWhile (EOp OLt [EDeref (EId "$i"), EId "$numArgs"]) $
        ESeq (setFieldT (primToStr (EDeref (EId "$i")))
                        (EGetField (EDeref $ EDeref $ EId"arguments")
                                   (primToStr (EDeref (EId "$i")))))
             (ESetRef (EId "$i")
                      (EOp ONumPlus [EDeref (EId "$i"), ENumber 1]))


--the pattern used to construct a regexp is in $regexpPattern,
--and the flags used for construction are in $regexpFlags. 
--these are used by Scheme's perl regexp thing 
jsRegExp = ERef $ object
  [ ("$proto", EId "$Function.prototype")
  , ("prototype", EId "$RegExp.prototype")
  , ("length", ENumber 2)
  , ("$code", constr) ]
 where
  constr = lambda ["$pattern", "$flags"] $ 
      ELet [("$P", pattern), ("$F", flags)] $
        checkFlags $
          setG $ setIC $ setML $
          setMatch $ setFlags $
          setSource $ setLI $
            ESeq (setFieldT (EString "$proto") (EId "$RegExp.prototype"))
                  (ESeq (setFieldT (EString "$class") (EString "RegExp"))
                       EUndefined)
  pattern = 
    EIf (isRefComb isObject (EId "$pattern"))
        (EIf (eNot (isUndefined (EId "$flags")))
             (EThrow $ newError "TypeError" "given regexp and flags in constr")
             (EGetField (EDeref (EId "$pattern"))
                        (EString "$regexpPattern")))
        (EIf (isUndefined (EId "$pattern"))
             (EString "")
             (toString (EId "$pattern")))
  --don't have to re-check the $flags being undefined here:
  flags = 
    EIf (isRefComb isObject (EId "$pattern"))
        (EGetField (EDeref (EId "$pattern"))
                   (EString "$regexpFlags"))
        (EIf (isUndefined (EId "$flags"))
             (EString "")
             (toString (EId "$flags")))
  checkFlags = id --TODO: throw type errors if wrong flags given (see 15.10.4.1)
  setG = fhelp "global" "g"
  setIC = fhelp "ignoreCase" "i"
  setML = fhelp "multiline" "m"
  fhelp fieldname flagname = 
    ESeq (setFieldT (EString fieldname)
                    (EOp OStrContains [EId "$F", EString flagname]))
  setMatch = ESeq (setFieldT (EString "$regexpPattern") (EId "$P"))
  setFlags = ESeq (setFieldT (EString "$regexpFlags") (EId "$F"))
  setSource = ESeq (setFieldT (EString "source") (EId "$P"))
  setLI = ESeq (setFieldT (EString "lastIndex") (ENumber 0))
               
 

-- |Sections 15.3.2 and 15.3.2
jsFunction = ERef $ object
  --special-case func constr to work as empty constr, as that is used
  --in some test cases and has no reason to evalbomb
  [ ("$code", lambda [] $
    ELet [("$numArgs", EGetField (EDeref $ EDeref $ EId "arguments")
                                 (EString "length"))] $
      EIf (eStxEq (EId "$numArgs") (ENumber 0))
          (setFieldTS (EString "$proto") (EId "$Function.prototype") $
           setFieldTS (EString "$class") (EString "Function") $
           setFieldTS (EString "length") (ENumber 0) $
           EUndefined)
          EEval)
   -- Both .prototype and .[[Prototype]] reference the same object.
  , ("$proto", EId "$Function.prototype")
  , ("$class", EString "Function") --TODO: not sure if this should be here
  , ("$strRep", EString $ nativeFunctionStrRep "Function")
  , ("prototype", EId "$Function.prototype")
  , ("length", ENumber 1)
  ]


jsBoolean = ERef $ object
  [ ("$proto", EId "$Function.prototype")
  , ("$class", EString "Function")
  , ("$strRep", EString $ nativeFunctionStrRep "Boolean")
  , ("prototype", EId "$Boolean.prototype")
  , ("length", ENumber 1)
  , ("$code", constr) ]
 where
  constr = lambda ["value"] $ 
    setFieldTS (EString "$proto") (EId "$Boolean.prototype") $
    setFieldTS (EString "$class") (EString "Boolean") $
    setFieldT  (EString "$value") (toBoolean (EId "value"))


--stringzzzz
--internal value held in $value
jsString = ERef $ object
  [ ("$proto", EId "$Function.prototype")
  , ("$class", EString "Function")
  , ("$strRep", EString $ nativeFunctionStrRep "String")
  , ("prototype", EId "$String.prototype")
  , ("fromCharCode", EString "TODO: String fromCharCode")
  , ("length", ENumber 1)
  , ("$code", lambda ["$value"] $ splitConstr constr func) ]
 where
  constr = 
    setFieldTS (EString "$proto") (EId "$String.prototype") $
    setFieldTS (EString "$class") (EString "String") $
    setFieldTS (EString "$value")
      (EIf (isUndefined (EId "$value")) (EString "") (toString (EId "$value")))$
    setFieldT  (EString "length") (EOp OStrLen [getFieldT (EString "$value")])
  func = 
    EIf (isUndefined $ EId "$value")
        (EString "")
        (toString (EId "$value"))

jsDate :: Expr
jsDate = ERef $ object
  [ ("$proto", EId "$Function.prototype")
  , ("$class", EString "Function")
  , ("$strRep", EString $ nativeFunctionStrRep "Date")
  , ("length", ENumber 7)
  , ("prototype", EId "$Date.prototype")
  , ("$code", constr)
  , ("parse", EString "TODO: Date.parse")
  , ("UTC", EString "TODO: Date.UTC")
  ]
 where
  constr = lambda ["y", "m", "d", "h", "min", "s", "ms"] $ 
    ELet [("$numArgs", EGetField (EDeref $ EDeref $ EId "arguments")
                                 (EString "length"))] $
      ESeq objsetup EUndefined  
  objsetup = 
    ESeq (setFieldT (EString "$class") (EString "Date"))
         (ESeq (setFieldT (EString "$proto") (EId "$Date.prototype"))
               (setFieldT (EString "$value") (EString "TODO:Dateimpl")))


jsNumber :: Expr
jsNumber = ERef $ object
  [ ("$proto", EId "$Function.prototype")
  , ("$class", EString "Function")
  , ("$strRep", EString $ nativeFunctionStrRep "Number")
  , ("length", ENumber 1)
  , ("prototype", EId "$Number.prototype")
  , ("$code", constr)
  , ("MAX_VALUE", ENumber (1.7976931348623157 * (10 ^ 308)))
  , ("MIN_VALUE", ENumber (5 * 1.0 / (10 ^ 324)))
  , ("NaN", ENumber (0.0/0.0))
  , ("NEGATIVE_INFINITY", ENumber (- (1.0 / 0.0)))
  , ("POSITIVE_INFINITY", ENumber (1.0 / 0.0))
  , ("parse", EString "TODO: Date.parse")
  , ("UTC", EString "TODO: Date.UTC")
  ]
 where
  constr = lambda ["$value"] $ 
    ELet [("$numArgs", EGetField (EDeref $ EDeref $ EId "arguments")
                                 (EString "length"))] $
      ESeq (EIf (eStxEq (EId "$numArgs") (ENumber 0))
                (objsetup (ENumber 0.0))
                (objsetup (toNumber $ EId "$value")))
           EUndefined
  objsetup val = 
    ESeq (setFieldT (EString "$class") (EString "Number"))
         (ESeq (setFieldT (EString "$proto") (EId "$Number.prototype"))
               (setFieldT (EString "$value") val))


-- |Section 15.3.4
-- TODO: call
functionPrototypeValues :: [(Ident,Expr)]
functionPrototypeValues = 
  [ -- In Safari 4.0, Function.prototype instanceof Object and not of Function
    ("$proto", EId "$Object.prototype")
  , ("$class", EString "Function")
  , ("$strRep", EString "function () {\n}")
  , ("constructor", EUndefined) -- Set to Function later
  , ("toString", functionObject [] $ getFieldT (EString "$strRep"))
  , ("length", ENumber 0)
  , ("apply", functionObject ["thisArg", "argArray"] $ 
    EIf (eNot (EOp OHasOwnProp [EDeref $ EId "this", EString "$code"]))
        (EThrow $ newError "TypeError" "apply must have this as a function") $
    ELet1 (EIf (eOr (isNull (EId "thisArg")) (isUndefined (EId "thisArg")))
               (EId "$global") (EId "thisArg")) $ \thisArg ->
    ELet1 (EIf (eOr (isNull (EId "argArray")) (isUndefined (EId "argArray")))
               (eArgumentsObj [] (EId "this"))
               (checkArray (EId "argArray") $ 
                arrayToArgs(EId "argArray") )) $ \argArray ->
      EApp (EGetField (EDeref $ EId "this") (EString "$code"))
           [EId thisArg, ERef $ EId argArray])
  ]
 where
  checkArray ae = 
    EIf (eNot (eAnd (isLocation ae) 
                    (eOr (hasClass ae "Array")
                         (eStxEq (getField ae (EString "$isArgs"))
                                 (EBool True)))))
        (EThrow $ newError "TypeError" "apply expects arguments or array")
  arrayToArgs ae = 
    --loop through the initial args obj, ae, and copy its elements into
    --the new one, argsObj, which starts off as an empty args object
    ELet2 (ERef (ENumber 0))(ERef$eArgumentsObj [] (EId "this")) $ \i argsObj ->
    ESeq ( 
      eFor EUndefined --init, incr, test, body
           (ESetRef (EId i) (EOp ONumPlus [EDeref (EId i), ENumber 1]))
           (EOp OLt [EDeref (EId i), EGetField (EDeref ae) (EString "length")])
           (ESeq (setField (EId argsObj) (primToStr (getField (EId argsObj) 
                                                      (EString "length")))
                           (EGetField (EDeref ae) (primToStr (EDeref $ EId i))))
                 (setField (EId argsObj) (EString "length")
                   (EOp ONumPlus [getField (EId argsObj) (EString "length"),
                                  ENumber 1]))))
      (EId argsObj)


hasClass eObj cls = eStxEq (getField eObj (EString "$class")) (EString cls)


-- |Section 15.6.4
booleanPrototype :: Expr
booleanPrototype = object
  [ ("$proto", EId "$Object.prototype")
  , ("$class", EString "Boolean")
  , ("$value", EBool False)
  , ("constructor", EUndefined) -- Set to Boolean later
  , ("toString", functionObject [] $ checkThis "Boolean" $
      EIf (getFieldT (EString "$value")) (EString "true") (EString "false"))
  , ("valueOf", functionObject [] $ checkThis "Boolean" $ 
      getFieldT (EString "$value"))
  ]


-- |Section 15.5.3.1
stringPrototype :: Expr
stringPrototype = object
  [ ("$proto", EId "$Object.prototype")
  , ("$class", EString "String") --yep, it's a string.
  , ("$value", EString "")
  , ("constructor", EUndefined) -- Set to String later
  , ("toString", tsvo)
  , ("valueOf", tsvo)
  , ("charAt", EString "TODO: String.prototype.charAt")
  , ("charCodeAt", EString "TODO: String.prototype.charCodeAt")
  , ("concat", EString "TODO: String.prototype.concat")
  , ("indexOf", EString "TODO: String.prototype.indexOf")
  , ("lastIndexOf", EString "TODO: String.prototype.lastIndexOf")
  , ("localeCompare", EString "TODO: String.prototype.localeCompare")
  , ("match", functionObject ["regexp"] $
      handleRegexp $ handleThis $
        EIf (toBoolean $ EGetField (EDeref $ EId "$regexp") (EString "global"))
            (EThrow $ EString "String.match w/ global #t NYI")
            (applyObj (EGetField (EDeref $ EId "$regexp") (EString "exec"))
                      (EId "$regexp")
                      [EId "$this"]))
  --TODO: do replace for real
  , ("replace", functionObject [] $
    (EGetField (EDeref $ EId "this") (EString "$value")))
  , ("search", EString "TODO: String.prototype.search")
  , ("slice", EString "TODO: String.prototype.slice")
  , ("split", functionObject ["separator", "limit"] $
    ELet [("$strThis", toString $ (EId "this"))] $
      EIf (eAnd (isObject (EId "separator"))
                (hasClass (EId "separator") "RegExp"))
       (eNewDirect (EDeref $ EId "Array") (ERef $ ERef $ 
         (EOp OStrSplitRegExp 
           [EId "$strThis", 
            getField (EId "separator") (EString "$regexpPattern")])))
       (eNewDirect (EDeref $ EId "Array") (ERef $ ERef $ 
         (EOp OStrSplitStrExp [EId "$strThis", toString $ (EId "separator")]))))
  , ("substring", EString "TODO: String.prototype.substring")
  , ("toLowerCase", EString "TODO: String.prototype.toLowerCase")
  , ("toLocaleLowerCase", EString "TODO: String.prototype.toLocaleLowerCase")
  , ("toUpperCase", EString "TODO: String.prototype.toUpperCase")
  , ("toLocaleUpperCase", EString "TODO: String.prototype.toLocaleUpperCase")
  , ("length", ENumber 0)
  ]
 where
  tsvo = functionObject [] $
    EIf (eNot (hasClass (EId "this") "String"))
        (EThrow $ newError "TypeError" "'this' from String's toString not str")
        (EGetField (EDeref $ EId "this") (EString "$value"))
  --String.match helpers:
  handleRegexp = ELet [("$regexp", 
    EIf (eAnd (isRefComb isObject (EId "regexp")) 
              (hasClass (EId "regexp") "RegExp"))
        (EId "regexp")
        (eNew (EDeref $ EId "RegExp") [EId "regexp"]))]
  handleThis = ELet [("$this", toString (EId "this"))]


numberPrototype :: Expr
numberPrototype = object
  [ ("$proto", EId "$Object.prototype")
  , ("$class", EString "Number")
  , ("$value", ENumber 0)
  , ("constructor", EUndefined) -- Set to Number later
  , ("toString", functionObject ["radix"] $ 
      EIf (eNot (eOr (eStxEq (EId "radix") EUndefined)
                     (eStxEq (EId "radix") (ENumber 10))))
          (EThrow $ EString "num toStr for non-10 radix NYI")
          (primToStr (getFieldT (EString "$value"))))
  , ("toLocaleString", functionObject [] $ 
      primToStr (getFieldT (EString "$value")))
  , ("valueOf", functionObject [] $ getFieldT (EString "$value"))
  , ("toFixed", functionObject [] $ EString "Number.toFixed")
  , ("toExponential", functionObject ["fracDigs"] $ EString "Number.toExp")
  , ("toPrecision", functionObject ["prec"] $ EString "Number.toPrecision")
  ]


datePrototype :: Expr
datePrototype = object
  [ ("$proto", EId "$Object.prototype")
  , ("$class", EString "Date")
  , ("$value", ENumber (0.0/0.0))
  , ("constructor", EUndefined) -- Set to Date later
  , ("toString", functionObject [] (EString "THIS IS A DATE"))
  , ("valueOf", functionObject [] (getFieldT (EString "$value")))
  , ("toDateString", functionObject [] $ EString "dateString")
  , ("toTimeString", functionObject [] $ EString "timeString")
  , ("toLocaleString", functionObject [] $ EString "localeString")
  , ("toLocaleDateString", functionObject [] $ EString "localeDateString")
  , ("toLocaleTimeString", functionObject [] $ EString "localeTimeString")
  , ("getTime", functionObject[]$checkThis"Date"$ getFieldT (EString "$value"))
  , ("getFullYear", nyi)
  , ("getUTCFullYear", nyi)
  , ("getMonth", nyi)
  , ("getUTCMonth", nyi)
  , ("getDate", nyi)
  , ("getUTCDate", nyi)
  , ("getDay", nyi)
  , ("getUTCDay", nyi)
  , ("getHours", nyi)
  , ("getUTCHours", nyi)
  , ("getMinutes", nyi)
  , ("getUTCMinutes", nyi)
  , ("getSeconds", nyi)
  , ("getUTCSeconds", nyi)
  , ("getMilliseconds", nyi)
  , ("getUTCMilliseconds", nyi)
  , ("getTimezoneOffset", nyi)
  , ("setTime", nyi)
  , ("setMilliseconds", nyi)
  , ("setUTCMilliseconds", nyi)
  , ("setSeconds", nyi)
  , ("setUTCSeconds", nyi)
  , ("setMinutes", nyi)
  , ("setUTCMinutes", nyi)
  , ("setHours", nyi)
  , ("setUTCHours", nyi)
  , ("setDate", nyi)
  , ("setUTCDate", nyi)
  , ("setMonth", nyi)
  , ("setUTCMonth", nyi)
  , ("setFullYear", nyi)
  , ("setUTCFullYear", nyi)
  , ("toUTCString", nyi)
  ]
 where
  nyi = functionObject [] $ EThrow $ EString "DATE FUNCS NYI"

--errors
--all errors are exactly the same, so these functions actually
--generate an error of a given name.
jsError protname = ERef $ object
  [ ("$proto", EId "$Function.prototype") 
  , ("$class", EString "Function")
  , ("$strRep", EString $ nativeFunctionStrRep "Error")
  , ("length", ENumber 1)
  , ("prototype", EId protname)
  , ("$code", lambda ["msg"] $
    ESeq (setFieldT (EString "$class") (EString "Error"))
         (ESeq (setFieldT (EString "$proto") (EId protname))
               (EIf (eNot (isUndefined (EId "msg")))
                    (setFieldT (EString "message") (toString $ EId "msg"))
                    EUndefined)))
  ]
errorPrototype name = object
  [ ("$proto", EId "$Object.prototype")
  , ("$class", EString "Error")
  , ("constructor", EUndefined) -- Set to be itself later
  , ("name", EString name)
  , ("message", EString (name ++ " error"))
  , ("toString", functionObject [] $ 
       EOp OStrPlus [toString $ getFieldT (EString "name"),
                     toString $ getFieldT (EString "message")])
  ]


setConstructors :: Expr
setConstructors = foldr ESeq EUndefined $ map doit
  ["Object", "Function", "Array", "String", "RegExp", "Date", "Boolean",
   "Number", "Error", "ConversionError", "EvalError", "RangeError",
   "ReferenceError", "SyntaxError", "TypeError", "URIError"]
 where
  doit name = ESetRef (EId ("$" ++ name ++ ".prototype"))
                (EUpdateField (EDeref $ EId ("$" ++ name ++ ".prototype"))
                              (EString "constructor")
                              (EDeref $ EId name))
  
ecma262Env :: Expr -> Expr
ecma262Env body = 
  --global is the initial object, at location 0
  ELet [("$global", ERef $ object [])] $
  --we immediately need function.prototype, since everything uses it
  ELet [("$Object.prototype", ERef $ object [])] $
  ELet [("$Function.prototype", ERef $ object [])] $

  ELet [("$makeException", 
              ELambda ["name", "msg"] $ eNew 
                (EGetField (EDeref $ EId "$global") (EId "name"))
                [EId "msg"])] $          

  updateObject (EId "$Object.prototype") objectPrototypeValues $
  updateObject (EId "$Function.prototype") functionPrototypeValues $
  ELet [("$Date.prototype", ERef datePrototype)] $
  ELet [("$Number.prototype", ERef numberPrototype)] $
  ELet [("$Array.prototype", ERef arrayPrototype)] $
  ELet [("$Boolean.prototype", ERef booleanPrototype)] $

  ELet [("$Error.prototype", ERef (errorPrototype "Error"))] $
  ELet [("$ConversionError.prototype", ERef(errorPrototype "ConversionError"))]$
  ELet [("$EvalError.prototype", ERef (errorPrototype "EvalError"))] $ 
  ELet [("$RangeError.prototype", ERef (errorPrototype "RangeError"))] $ 
  ELet [("$ReferenceError.prototype", ERef (errorPrototype "ReferenceError"))]$
  ELet [("$SyntaxError.prototype", ERef (errorPrototype "SyntaxError"))] $ 
  ELet [("$TypeError.prototype", ERef (errorPrototype "TypeError"))] $ 
  ELet [("$URIError.prototype", ERef (errorPrototype "URIError"))] $ 

  ELet [("Object", ERef jsObject)] $
  ELet [("Function", ERef jsFunction)] $
  ELet [("Array", ERef jsArray)] $
  --regexp.proto uses Array, so it must come after
  ELet [("$RegExp.prototype", ERef regExpPrototype)] $
  ELet [("RegExp", ERef jsRegExp)] $
  ELet [("Date", ERef jsDate)] $
  ELet [("Number", ERef jsNumber)] $
  --string.proto uses RegExp, so it must come after it.
  ELet [("$String.prototype", ERef stringPrototype)] $
  ELet [("String", ERef jsString)] $
  ELet [("Boolean", ERef jsBoolean)] $
  
  ELet [("Error", ERef (jsError "$Error.prototype"))] $ 
  ELet [("ConversionError", ERef (jsError "$ConversionError.prototype"))] $ 
  ELet [("EvalError", ERef (jsError "$EvalError.prototype"))] $ 
  ELet [("RangeError", ERef (jsError "$RangeError.prototype"))] $ 
  ELet [("ReferenceError", ERef (jsError "$ReferenceError.prototype"))] $ 
  ELet [("SyntaxError", ERef (jsError "$SyntaxError.prototype"))] $ 
  ELet [("TypeError", ERef (jsError "$TypeError.prototype"))] $ 
  ELet [("URIError", ERef (jsError "$URIError.prototype"))] $ 

  ESeq setConstructors $
  updateObject (EId "$global") globalValuesAndFunctions $
  ELet [("this", EId "$global")] $
  body
