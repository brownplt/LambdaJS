module BrownPLT.JavaScript.Semantics.ECMAEnvironment
  ( ecma262Env
  ) where

import BrownPLT.JavaScript.Semantics.Desugar
import BrownPLT.JavaScript.Semantics.Syntax
import Text.ParserCombinators.Parsec
import BrownPLT.JavaScript.Parser (parseExpression)
import qualified Data.Map as M

-- |According to the specification, toPrimitive may signal a TypeError.
-- this is generalized to do either toString first, or valueOf first,
-- based on the 'hint'
-- Even though GetValue'd values are given to ToPrimitive in ECMA,
-- here we need ERefs because we will apply functions.
-- So make sure you give this ERef (EObject) if you get an object.
toPrimitive' :: String -> String -> ExprPos
toPrimitive' first second = 
  --if it's an object ref, then convert it with methods
  --otherwise it is already primitive, so just return it.
  ELambda nopos ["$x"] $ 
    EIf nopos (isLocation (EId nopos "$x"))
        cvt
        (EId nopos "$x")
  -- [[DefaultValue]] (8.6.2.6)
  where 
    --if valueOf is a function, try it. else try tostr.
    cvt = ELet nopos [("$vOf", (EGetField nopos (EDeref nopos (EId nopos "$x")) (EString nopos first)))] $    
            EIf nopos (isRefComb isFunctionObj (EId nopos "$vOf"))
              (ELet nopos [("$vRes", applyObj (EId nopos "$vOf") (EId nopos "$x") [])] $
                EIf nopos (isPrim (EId nopos "$vRes"))
                    (EId nopos "$vRes")
                    str)
              str
    --if toString is a function, try it. else throw excp
    str = ELet nopos [("$toStr", (EGetField nopos (EDeref nopos (EId nopos "$x")) (EString nopos second)))] $
            EIf nopos (isRefComb isFunctionObj (EId nopos "$toStr"))
              (ELet nopos [("$tRes", applyObj (EId nopos "$toStr") (EId nopos "$x") [])] $
                EIf nopos (isPrim (EId nopos "$tRes"))
                    (EId nopos "$tRes")
                    exc)
              exc
    exc = (EThrow nopos $ newError "TypeError" "cannot convert obj to primitive")



object :: [(Ident, ExprPos)] -> ExprPos
object props = EObject nopos $ map (\(x, e) -> (x, e)) props


-- |helper to have already bound IDs
lambda :: [Ident] -> ExprPos -> ExprPos
lambda args body = ELambda nopos ["this", "arguments"] body'
  where body' = ELet nopos (map arg (zip args [0..])) body
        arg (x,n) = (x,EGetField nopos (EDeref nopos (EDeref nopos (EId nopos "arguments")))
                                   (EString nopos (show n)))
-- |Wraps the body of a lambda expression into a function object
functionObject :: [Ident] -> ExprPos -> ExprPos
functionObject args body = ERef nopos $ object 
  [ ("$code", lambda args body)
  , ("arguments", ENull nopos)
  , ("prototype", ERef nopos $ object [("$proto", EId nopos "@Object_prototype")])
--  , ("$class", EString "Function")
  , ("$proto", EId nopos "@Function_prototype")
  , ("length", ENumber nopos (fromIntegral $ length args))
  , ("$strRep", EString nopos "function fromafunctionboject(){}")
  ]


--evaluates the 1st expr if the function was called as a constructor,
--and the 2nd if it was called as a function
splitConstr :: ExprPos -> ExprPos -> ExprPos
splitConstr eConstr eFunc = 
  EIf nopos (eNot (isUndefined $ getFieldT (EString nopos "$constructing")))
      eConstr
      eFunc
      


asVariables :: [(Ident, ExprPos)] -> [(Ident, ExprPos)]
asVariables binds = map (\(x, e) -> (x, ERef nopos e)) binds


-- |Section 15.1
globalValuesAndFunctions :: [(Ident, ExprPos)] 
globalValuesAndFunctions = 
  [ ("$proto", EId nopos "@Object_prototype")
  , ("$class", EString nopos "global")
  , ("NaN", ENumber nopos (0.0/0.0))
  , ("Infinity", ENumber nopos (1.0/0.0))
  , ("undefined", EUndefined nopos)
  -- TODO: parseInt and parseFloat are oversimplified
  , ("parseInt", functionObject ["n"] $ 
    EOp nopos OPrimToNum [toString $ EId nopos "n"])
  , ("parseFloat", functionObject ["n"] $ 
    EOp nopos OPrimToNum [toString $ EId nopos "n"])
  , ("isNaN", functionObject ["n"] $ 
       eStxEq (ENumber nopos (0.0/0.0)) (toNumber (EId nopos "n")))
  , ("isFinite", functionObject ["x"] $
     ELet nopos [("n", toNumber (EId nopos "x"))] $
       EIf nopos (eStxEq (EId nopos "n") (ENumber nopos (0.0/0.0))) (EBool nopos False) $
       EIf nopos (eStxEq (EId nopos "n") (ENumber nopos (1.0/0.0))) (EBool nopos False) $
       EIf nopos (eStxEq (EId nopos "n") (ENumber nopos (-1.0/0.0))) (EBool nopos False) $
       (EBool nopos True))
  -- TODO: URI functions don't transform URLs correctly.  But, the type
  -- conversion is in place.
  , ("decodeURI", functionObject ["encodedURI"] $
     toString $ EId nopos "decodeURI")
  , ("decodeURIComponent", functionObject ["encodedURIComponent"] $
      toString $ EId nopos "encodedURIComponent")
  , ("encodeURI", functionObject ["uri"] $
      toString $ EId nopos "uri")
  , ("encodeURIComponent", functionObject ["uriComponent"] $
      toString $ EId nopos "uriComponent")
  , ("eval", functionObject [] (EEval nopos))
  --these are refs of refs, so we must deref:
  , ("Object", EDeref nopos $ EId nopos "Object")
  , ("Function", EDeref nopos $ EId nopos "Function")
  , ("Array", EDeref nopos $ EId nopos "Array")
  , ("RegExp", EDeref nopos $ EId nopos "RegExp")
  , ("String", EDeref nopos $ EId nopos "String")
  , ("Date", EDeref nopos $ EId nopos "Date")
  , ("Number", EDeref nopos $ EId nopos "Number")
  , ("Boolean", EDeref nopos $ EId nopos "Boolean")
  
  , ("Error", EDeref nopos $ EId nopos "Error")
  , ("ConversionError", EDeref nopos $ EId nopos "ConversionError")
  , ("EvalError", EDeref nopos $ EId nopos "EvalError")
  , ("RangeError", EDeref nopos $ EId nopos "RangeError")
  , ("ReferenceError", EDeref nopos $ EId nopos "ReferenceError")
  , ("SyntaxError", EDeref nopos $ EId nopos "SyntaxError")
  , ("TypeError", EDeref nopos $ EId nopos "TypeError")
  , ("URIError", EDeref nopos $ EId nopos "URIError")

  , ("print", functionObject ["V"] $ EOp nopos OPrint [toString (EId nopos "V")])
  , ("Math", ERef nopos $ object $
    [ ("$class", EString nopos "Math")
    , ("$proto", EId nopos "@Object_prototype") 
    , ("E", ENumber nopos (exp 1))
    , ("LN10", ENumber nopos (log 10))
    , ("LN2", ENumber nopos (log 2))
    , ("LOG2E", ENumber nopos (log (exp 1) / log 2))
    , ("LOG10E", ENumber nopos (log (exp 1) / log 10))
    , ("PI", ENumber nopos pi)
    , ("SQRT1_2", ENumber nopos (sqrt (1.0/2.0)))
    , ("SQRT2", ENumber nopos (sqrt 2))

    , ("exp", mathFunc OMathExp)
    , ("log", mathFunc OMathLog)
    , ("sin", mathFunc OMathSin)
    , ("cos", mathFunc OMathCos)
    , ("abs", mathFunc OMathAbs)
    , ("pow", mathFunc2 OMathPow)
    ])  
  ]
 where
  mathFunc op = functionObject ["x"] (EOp nopos op [toNumber (EId nopos "x")])
  mathFunc2 op = functionObject ["x","y"] (EOp nopos op [toNumber (EId nopos "x"),
                                                   toNumber (EId nopos "y")])

--update the object with everything in the given list
--used to close recursions
updateObject :: ExprPos -> [(Ident, ExprPos)] -> ExprPos -> ExprPos
updateObject objE [] rest = rest
updateObject objE ((name,e):xs) rest = 
  ESeq nopos (setField objE (EString nopos name) e)
           (updateObject objE xs rest)

--helper to ensure the corrakt type of 'this'
checkThis expected = EIf nopos (eNot (eStxEq (getFieldT (EString nopos "$class")) 
                                       (EString nopos expected)))
                (EThrow nopos $ newError "TypeError" $ 
                  "expected " ++ expected ++ " obj, got smth else")

-- |Sections 15.2.3 and 15.2.4
-- TODO : isPrototypeOf and propertyIsEnumerable
objectPrototypeValues =
  [ ("$proto", ENull nopos)
  , ("$class", EString nopos "Object")
  , ("constructor", EUndefined nopos) -- Set to Object later
  , ("toString", functionObject [] $
       EOp nopos OStrPlus [EString nopos "[object ",
                     EOp nopos OStrPlus [EGetField nopos (EDeref nopos $ EId nopos "this") 
                                             (EString nopos "$class"),
                                   EString nopos "]"]])
  , ("toLocaleString", functionObject [] $
       EOp nopos OStrPlus [EString nopos "[object ",
                     EOp nopos OStrPlus [EGetField nopos (EDeref nopos $ EId nopos "this") 
                                             (EString nopos "$class"),
                                   EString nopos "]"]])
  , ("valueOf", functionObject [] $ EId nopos "this")
  , ("hasOwnProperty", functionObject ["V"] $
       EOp nopos OHasOwnProp [EDeref nopos $ EId nopos "this",
                        toString (EId nopos "V")])
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
arrayPrototype :: ExprPos
arrayPrototype = object
  [ ("$proto", EId nopos "@Object_prototype")
  , ("$class", EString nopos "Object")
  , ("length", ENumber nopos 0)
  , ("constructor", EUndefined nopos) -- Set to Array later
  , ("toString", functionObject [] $ checkThis "Array" $ 
      applyObj (EGetField nopos (EDeref nopos $ EId nopos "this") (EString nopos "join")) 
               (EId nopos "this") [])
  , ("toLocaleString", desugarExprSetenv arrayJoinLocale 
                         (M.singleton "this" True))
  , ("concat", (EString nopos "TODO: Array.prototype.concat"))
  , ("join", desugarExprSetenv arrayJoin (M.singleton "this" True))
  , ("pop", functionObject [] $
    (EIf nopos (eStxEq (getFieldT (EString nopos "length")) (ENumber nopos 0))
         (EUndefined nopos) $
         --set length to length-1, get the item there, delete it, and return
         ELet nopos [("$newlen", (EOp nopos ONumPlus 
           [primToNum (getFieldT (EString nopos "length")), ENumber nopos (-1)]))] $
           ELet nopos [("$result", getFieldT (primToStr (EId nopos "$newlen")))] $
             ESeq nopos (setFieldT (EString nopos "length") (EId nopos "$newlen")) $
               ESeq nopos (ESetRef nopos (EId nopos "this")
                      (EDeleteField nopos (EDeref nopos $ EId nopos "this")
                                    (primToStr $ EId nopos "$newlen")))
                    (EId nopos "$result")))
  , ("push", functionObject [] $ --use a for loop:
    ELet nopos [("$i", ERef nopos (ENumber nopos 0))] $ ESeq nopos ( 
      eFor (EUndefined nopos) --init, incr, test, body
           (ESetRef nopos (EId nopos "$i") (EOp nopos ONumPlus [EDeref nopos (EId nopos "$i"), ENumber nopos 1]))
           (EOp nopos OLt [EDeref nopos (EId nopos "$i"),
                     EGetField nopos (EDeref nopos (EDeref nopos (EId nopos "arguments"))) 
                               (EString nopos "length")])
           (ESeq nopos (setFieldT (primToStr (getFieldT (EString nopos "length")) )
                            (EGetField nopos (EDeref nopos (EDeref nopos (EId nopos "arguments")))
                                       (primToStr (EDeref nopos $ EId nopos "$i"))))
                 (setFieldT (EString nopos "length")
                            (EOp nopos ONumPlus [getFieldT (EString nopos "length"),
                                          ENumber nopos 1]))))
           (getFieldT (EString nopos "length"))) --return the new length
  , ("reverse", (EString nopos "TODO: Array.prototype.reverse"))
  , ("shift", (EString nopos "TODO: Array.prototype.shift"))
  , ("slice", (EString nopos "TODO: Array.prototype.slice"))
  , ("sort", desugarExprSetenv arraySort (M.singleton "this" True))
  , ("splice", (EString nopos "TODO: Array.prototype.splice"))
  , ("unshift", (EString nopos "TODO: Array.prototype.unshift"))
  ]
  
-- |Section 15.4.4
regExpPrototype :: ExprPos
regExpPrototype = object
  [ ("$proto", EId nopos "@Object_prototype")
  , ("$class", EString nopos "Object")
  , ("length", ENumber nopos 0)
  , ("constructor", EUndefined nopos) -- Set to RegExp later
  --, ("toString", (EString nopos "TODO: regExp.prototype.toString"))
  --TODO: make this return an array with 'index' and 'input'
  , ("exec", functionObject ["$$string"] $ checkThis "RegExp" $ 
    EIf nopos (eOr (getFieldT (EString nopos "global"))
             (getFieldT (EString nopos "ignoreCase")))
      (EThrow nopos (EString nopos "regexp not fully impl yet")) $
      ELet1 nopos (toString $ EId nopos "$$string") (\str -> 
        ELet1 nopos (EOp nopos ORegExpMatch [EId nopos str, getFieldT (EString nopos "$regexpPattern")])
          (\matchRes -> EIf nopos (isUndefined (EId nopos matchRes)) (ENull nopos) $
            eNewDirect (EDeref nopos $ EId nopos "Array") (ERef nopos $ ERef nopos $ EId nopos matchRes))))
  , ("test", EString nopos "TODO: RegExp.prototype.test")
  ]


-- |Sections 15.2.1 and 15.2.2
jsObject :: ExprPos
jsObject = ERef nopos $ object
  [ ("$proto", EId nopos "@Function_prototype") -- Yes, this is correct.
  , ("prototype", EId nopos "@Object_prototype")
  , ("length", ENumber nopos 1)
  , ("$code", lambda ["value"] $ 
       EIf nopos (EIf nopos (EOp nopos OStrictEq [EId nopos "value", (EUndefined nopos)])
                (EBool nopos True)
                (EOp nopos OStrictEq [EId nopos "value", ENull nopos]))
           (ERef nopos $ object [ ("$class", EString nopos "Object")
                          , ("$proto", EId nopos "@Object_prototype")
                          ])
           (toObject (EId nopos "value")))
  ]


--helpers for constructors:
setField lhse fnamee fe =
  ESetRef nopos lhse (EUpdateField nopos (EDeref nopos lhse) fnamee fe)
setFieldT = setField (EId nopos "this")
setFieldTS a b = ESeq nopos $ setField (EId nopos "this") a b
getField lhse fnamee = EGetField nopos (EDeref nopos lhse) fnamee
getFieldT = getField (EId nopos "this")

-- |Section 15.4.2
-- TODO: make it work as a non-constr too
jsArray :: ExprPos
jsArray = ERef nopos $ object
  [ ("$proto", EId nopos "@Function_prototype")
  , ("length", ENumber nopos 1)
  , ("prototype", EId nopos "$Array.prototype")
  , ("$strRep", EString nopos $ nativeFunctionStrRep "Array")
  --15.4.2.1
  , ("$code", constr)
  ]
 where
  constr = lambda ["$arg0"] $ 
    ELet nopos [("$numArgs", EGetField nopos (EDeref nopos $ EDeref nopos $ EId nopos "arguments")
                                 (EString nopos "length"))] $
      splitConstr asConstr asFunc
  asFunc = eNewDirect (getField (EId nopos "$global") (EString nopos "Array")) 
             (EId nopos "arguments")
  asConstr = 
      --if there is 1 arg and it is a number, we do something else:
      EIf nopos (eAnd (eStxEq (EId nopos "$numArgs") (ENumber nopos 1))
                (isNumber (EId nopos "$arg0")))
          (EIf nopos (eStxEq (EOp nopos OToUInt32 [(EId nopos "$arg0")])
                       (EId nopos "$arg0"))
               (objsetup (EId nopos "$arg0") (EUndefined nopos))
               (EThrow nopos $ newError "RangeError" "invalid len to new Array()"))
          --otherwise we do this:
          (objsetup (EId nopos "$numArgs") objconstr)
  objsetup lengthe r = 
    ESeq nopos (setFieldT (EString nopos "$class") (EString nopos "Array"))
         (ESeq nopos (setFieldT (EString nopos "$proto") (EId nopos "$Array.prototype"))
               (ESeq nopos (setFieldT (EString nopos "length") lengthe)
                     r))
  objconstr = 
    ELet nopos [("$i", ERef nopos $ ENumber nopos 0)] $
      EWhile nopos (EOp nopos OLt [EDeref nopos (EId nopos "$i"), EId nopos "$numArgs"]) $
        ESeq nopos (setFieldT (primToStr (EDeref nopos (EId nopos "$i")))
                        (EGetField nopos (EDeref nopos $ EDeref nopos $ EId nopos"arguments")
                                   (primToStr (EDeref nopos (EId nopos "$i")))))
             (ESetRef nopos (EId nopos "$i")
                      (EOp nopos ONumPlus [EDeref nopos (EId nopos "$i"), ENumber nopos 1]))


--the pattern used to construct a regexp is in $regexpPattern,
--and the flags used for construction are in $regexpFlags. 
--these are used by Scheme's perl regexp thing 
jsRegExp = ERef nopos $ object
  [ ("$proto", EId nopos "@Function_prototype")
  , ("prototype", EId nopos "$RegExp.prototype")
  , ("length", ENumber nopos 2)
  , ("$code", constr) ]
 where
  constr = lambda ["$pattern", "$flags"] $ 
      ELet nopos [("$P", pattern), ("$F", flags)] $
        checkFlags $
          setG $ setIC $ setML $
          setMatch $ setFlags $
          setSource $ setLI $
            ESeq nopos (setFieldT (EString nopos "$proto") (EId nopos "$RegExp.prototype"))
                  (ESeq nopos (setFieldT (EString nopos "$class") (EString nopos "RegExp"))
                       (EUndefined nopos))
  pattern = 
    EIf nopos (isRefComb isObject (EId nopos "$pattern"))
        (EIf nopos (eNot (isUndefined (EId nopos "$flags")))
             (EThrow nopos $ newError "TypeError" "given regexp and flags in constr")
             (EGetField nopos (EDeref nopos (EId nopos "$pattern"))
                        (EString nopos "$regexpPattern")))
        (EIf nopos (isUndefined (EId nopos "$pattern"))
             (EString nopos "")
             (toString (EId nopos "$pattern")))
  --don't have to re-check the $flags being undefined here:
  flags = 
    EIf nopos (isRefComb isObject (EId nopos "$pattern"))
        (EGetField nopos (EDeref nopos (EId nopos "$pattern"))
                   (EString nopos "$regexpFlags"))
        (EIf nopos (isUndefined (EId nopos "$flags"))
             (EString nopos "")
             (toString (EId nopos "$flags")))
  checkFlags = id --TODO: throw type errors if wrong flags given (see 15.10.4.1)
  setG = fhelp "global" "g"
  setIC = fhelp "ignoreCase" "i"
  setML = fhelp "multiline" "m"
  fhelp fieldname flagname = 
    ESeq nopos (setFieldT (EString nopos fieldname)
                    (EOp nopos OStrContains [EId nopos "$F", EString nopos flagname]))
  setMatch = ESeq nopos (setFieldT (EString nopos "$regexpPattern") (EId nopos "$P"))
  setFlags = ESeq nopos (setFieldT (EString nopos "$regexpFlags") (EId nopos "$F"))
  setSource = ESeq nopos (setFieldT (EString nopos "source") (EId nopos "$P"))
  setLI = ESeq nopos (setFieldT (EString nopos "lastIndex") (ENumber nopos 0))
               
 

-- |Sections 15.3.2 and 15.3.2
jsFunction = ERef nopos $ object
  --special-case func constr to work as empty constr, as that is used
  --in some test cases and has no reason to evalbomb
  [ ("$code", lambda [] $
    ELet nopos [("$numArgs", EGetField nopos (EDeref nopos $ EDeref nopos $ EId nopos "arguments")
                                 (EString nopos "length"))] $
      EIf nopos (eStxEq (EId nopos "$numArgs") (ENumber nopos 0))
          (setFieldTS (EString nopos "$proto") (EId nopos "@Function_prototype") $
           setFieldTS (EString nopos "$class") (EString nopos "Function") $
           setFieldTS (EString nopos "length") (ENumber nopos 0) $
           (EUndefined nopos))
          (EEval nopos))
   -- Both .prototype and .[[Prototype]] reference the same object.
  , ("$proto", EId nopos "@Function_prototype")
  , ("$class", EString nopos "Function") --TODO: not sure if this should be here
  , ("$strRep", EString nopos $ nativeFunctionStrRep "Function")
  , ("prototype", EId nopos "@Function_prototype")
  , ("length", ENumber nopos 1)
  ]


jsBoolean = ERef nopos $ object
  [ ("$proto", EId nopos "@Function_prototype")
  , ("$class", EString nopos "Function")
  , ("$strRep", EString nopos $ nativeFunctionStrRep "Boolean")
  , ("prototype", EId nopos "$Boolean.prototype")
  , ("length", ENumber nopos 1)
  , ("$code", constr) ]
 where
  constr = lambda ["value"] $ 
    setFieldTS (EString nopos "$proto") (EId nopos "$Boolean.prototype") $
    setFieldTS (EString nopos "$class") (EString nopos "Boolean") $
    setFieldT  (EString nopos "$value") (toBoolean (EId nopos "value"))


--stringzzzz
--internal value held in $value
jsString = ERef nopos $ object
  [ ("$proto", EId nopos "@Function_prototype")
  , ("$class", EString nopos "Function")
  , ("$strRep", EString nopos $ nativeFunctionStrRep "String")
  , ("prototype", EId nopos "$String.prototype")
  , ("fromCharCode", EString nopos "TODO: String fromCharCode")
  , ("length", ENumber nopos 1)
  , ("$code", lambda ["$value"] $ splitConstr constr func) ]
 where
  constr = 
    setFieldTS (EString nopos "$proto") (EId nopos "$String.prototype") $
    setFieldTS (EString nopos "$class") (EString nopos "String") $
    setFieldTS (EString nopos "$value")
      (EIf nopos (isUndefined (EId nopos "$value")) (EString nopos "") (toString (EId nopos "$value")))$
    setFieldT  (EString nopos "length") (EOp nopos OStrLen [getFieldT (EString nopos "$value")])
  func = 
    EIf nopos (isUndefined $ EId nopos "$value")
        (EString nopos "")
        (toString (EId nopos "$value"))

jsDate :: ExprPos
jsDate = ERef nopos $ object
  [ ("$proto", EId nopos "@Function_prototype")
  , ("$class", EString nopos "Function")
  , ("$strRep", EString nopos $ nativeFunctionStrRep "Date")
  , ("length", ENumber nopos 7)
  , ("prototype", EId nopos "$Date.prototype")
  , ("$code", constr)
  , ("parse", EString nopos "TODO: Date.parse")
  , ("UTC", EString nopos "TODO: Date.UTC")
  ]
 where
  constr = lambda ["y", "m", "d", "h", "min", "s", "ms"] $ 
    ELet nopos [("$numArgs", EGetField nopos (EDeref nopos $ EDeref nopos $ EId nopos "arguments")
                                 (EString nopos "length"))] $
      ESeq nopos objsetup (EUndefined nopos)
  objsetup = 
    ESeq nopos (setFieldT (EString nopos "$class") (EString nopos "Date"))
         (ESeq nopos (setFieldT (EString nopos "$proto") (EId nopos "$Date.prototype"))
               (setFieldT (EString nopos "$value") (EString nopos "TODO:Dateimpl")))


jsNumber :: ExprPos
jsNumber = ERef nopos $ object
  [ ("$proto", EId nopos "@Function_prototype")
  , ("$class", EString nopos "Function")
  , ("$strRep", EString nopos $ nativeFunctionStrRep "Number")
  , ("length", ENumber nopos 1)
  , ("prototype", EId nopos "$Number.prototype")
  , ("$code", constr)
  , ("MAX_VALUE", ENumber nopos (1.7976931348623157 * (10 ^ 308)))
  , ("MIN_VALUE", ENumber nopos (5 * 1.0 / (10 ^ 324)))
  , ("NaN", ENumber nopos (0.0/0.0))
  , ("NEGATIVE_INFINITY", ENumber nopos (- (1.0 / 0.0)))
  , ("POSITIVE_INFINITY", ENumber nopos (1.0 / 0.0))
  , ("parse", EString nopos "TODO: Date.parse")
  , ("UTC", EString nopos "TODO: Date.UTC")
  ]
 where
  constr = lambda ["$value"] $ 
    ELet nopos [("$numArgs", EGetField nopos (EDeref nopos $ EDeref nopos $ EId nopos "arguments")
                                 (EString nopos "length"))] $
      ESeq nopos (EIf nopos (eStxEq (EId nopos "$numArgs") (ENumber nopos 0))
                (objsetup (ENumber nopos 0.0))
                (objsetup (toNumber $ EId nopos "$value")))
           (EUndefined nopos)
  objsetup val = 
    ESeq nopos (setFieldT (EString nopos "$class") (EString nopos "Number"))
         (ESeq nopos (setFieldT (EString nopos "$proto") (EId nopos "$Number.prototype"))
               (setFieldT (EString nopos "$value") val))


-- |Section 15.3.4
-- TODO: call
functionPrototypeValues :: [(Ident,ExprPos)]
functionPrototypeValues = 
  [ -- In Safari 4.0, Function.prototype instanceof Object and not of Function
    ("$proto", EId nopos "@Object_prototype")
  , ("$class", EString nopos "Function")
  , ("$strRep", EString nopos "function () {\n}")
  , ("constructor", EUndefined nopos) -- Set to Function later
  , ("toString", functionObject [] $ getFieldT (EString nopos "$strRep"))
  , ("length", ENumber nopos 0)
  , ("apply", functionObject ["thisArg", "argArray"] $ 
    EIf nopos (eNot (EOp nopos OHasOwnProp [EDeref nopos $ EId nopos "this", EString nopos "$code"]))
        (EThrow nopos $ newError "TypeError" "apply must have this as a function") $
    ELet1 nopos (EIf nopos (eOr (isNull (EId nopos "thisArg")) (isUndefined (EId nopos "thisArg")))
               (EId nopos "$global") (EId nopos "thisArg")) $ \thisArg ->
    ELet1 nopos (EIf nopos (eOr (isNull (EId nopos "argArray")) (isUndefined (EId nopos "argArray")))
               (eArgumentsObj [] (EId nopos "this"))
               (checkArray (EId nopos "argArray") $ 
                arrayToArgs(EId nopos "argArray") )) $ \argArray ->
      EApp nopos (EGetField nopos (EDeref nopos $ EId nopos "this") (EString nopos "$code"))
           [EId nopos thisArg, ERef nopos $ EId nopos argArray])
  ]
 where
  checkArray ae = 
    EIf nopos (eNot (eAnd (isLocation ae) 
                    (eOr (hasClass ae "Array")
                         (eStxEq (getField ae (EString nopos "$isArgs"))
                                 (EBool nopos True)))))
        (EThrow nopos $ newError "TypeError" "apply expects arguments or array")
  arrayToArgs ae = 
    --loop through the initial args obj, ae, and copy its elements into
    --the new one, argsObj, which starts off as an empty args object
    ELet2 nopos (ERef nopos (ENumber nopos 0))(ERef nopos$eArgumentsObj [] (EId nopos "this")) $ \i argsObj ->
    ESeq nopos ( 
      eFor (EUndefined nopos) --init, incr, test, body
           (ESetRef nopos (EId nopos i) (EOp nopos ONumPlus [EDeref nopos (EId nopos i), ENumber nopos 1]))
           (EOp nopos OLt [EDeref nopos (EId nopos i), EGetField nopos (EDeref nopos ae) (EString nopos "length")])
           (ESeq nopos (setField (EId nopos argsObj) (primToStr (getField (EId nopos argsObj) 
                                                      (EString nopos "length")))
                           (EGetField nopos (EDeref nopos ae) (primToStr (EDeref nopos $ EId nopos i))))
                 (setField (EId nopos argsObj) (EString nopos "length")
                   (EOp nopos ONumPlus [getField (EId nopos argsObj) (EString nopos "length"),
                                  ENumber nopos 1]))))
      (EId nopos argsObj)


hasClass eObj cls = eStxEq (getField eObj (EString nopos "$class")) (EString nopos cls)


-- |Section 15.6.4
booleanPrototype :: ExprPos
booleanPrototype = object
  [ ("$proto", EId nopos "@Object_prototype")
  , ("$class", EString nopos "Boolean")
  , ("$value", EBool nopos False)
  , ("constructor", EUndefined nopos) -- Set to Boolean later
  , ("toString", functionObject [] $ checkThis "Boolean" $
      EIf nopos (getFieldT (EString nopos "$value")) (EString nopos "true") (EString nopos "false"))
  , ("valueOf", functionObject [] $ checkThis "Boolean" $ 
      getFieldT (EString nopos "$value"))
  ]


-- |Section 15.5.3.1
stringPrototype :: ExprPos
stringPrototype = object
  [ ("$proto", EId nopos "@Object_prototype")
  , ("$class", EString nopos "String") --yep, it's a string.
  , ("$value", EString nopos "")
  , ("constructor", EUndefined nopos) -- Set to String later
  , ("toString", tsvo)
  , ("valueOf", tsvo)
  , ("charAt", EString nopos "TODO: String.prototype.charAt")
  , ("charCodeAt", EString nopos "TODO: String.prototype.charCodeAt")
  , ("concat", EString nopos "TODO: String.prototype.concat")
  , ("indexOf", EString nopos "TODO: String.prototype.indexOf")
  , ("lastIndexOf", EString nopos "TODO: String.prototype.lastIndexOf")
  , ("localeCompare", EString nopos "TODO: String.prototype.localeCompare")
  , ("match", functionObject ["regexp"] $
      handleRegexp $ handleThis $
        EIf nopos (toBoolean $ EGetField nopos (EDeref nopos $ EId nopos "$regexp") (EString nopos "global"))
            (EThrow nopos $ EString nopos "String.match w/ global #t NYI")
            (applyObj (EGetField nopos (EDeref nopos $ EId nopos "$regexp") (EString nopos "exec"))
                      (EId nopos "$regexp")
                      [EId nopos "$this"]))
  --TODO: do replace for real
  , ("replace", functionObject [] $
    (EGetField nopos (EDeref nopos $ EId nopos "this") (EString nopos "$value")))
  , ("search", EString nopos "TODO: String.prototype.search")
  , ("slice", EString nopos "TODO: String.prototype.slice")
  , ("split", functionObject ["separator", "limit"] $
    ELet nopos [("$strThis", toString $ (EId nopos "this"))] $
      EIf nopos (eAnd (isObject (EId nopos "separator"))
                (hasClass (EId nopos "separator") "RegExp"))
       (eNewDirect (EDeref nopos $ EId nopos "Array") (ERef nopos $ ERef nopos $ 
         (EOp nopos OStrSplitRegExp 
           [EId nopos "$strThis", 
            getField (EId nopos "separator") (EString nopos "$regexpPattern")])))
       (eNewDirect (EDeref nopos $ EId nopos "Array") (ERef nopos $ ERef nopos $ 
         (EOp nopos OStrSplitStrExp [EId nopos "$strThis", toString $ (EId nopos "separator")]))))
  , ("substring", EString nopos "TODO: String.prototype.substring")
  , ("toLowerCase", EString nopos "TODO: String.prototype.toLowerCase")
  , ("toLocaleLowerCase", EString nopos "TODO: String.prototype.toLocaleLowerCase")
  , ("toUpperCase", EString nopos "TODO: String.prototype.toUpperCase")
  , ("toLocaleUpperCase", EString nopos "TODO: String.prototype.toLocaleUpperCase")
  , ("length", ENumber nopos 0)
  ]
 where
  tsvo = functionObject [] $
    EIf nopos (eNot (hasClass (EId nopos "this") "String"))
            (EThrow nopos $ newError "TypeError" "'this' from String's toString not str")
            (EGetField nopos (EDeref nopos $ EId nopos "this") (EString nopos "$value"))
  --String.match helpers:
  handleRegexp = ELet nopos [("$regexp", 
    EIf nopos (eAnd (isRefComb isObject (EId nopos "regexp")) 
              (hasClass (EId nopos "regexp") "RegExp"))
        (EId nopos "regexp")
        (eNew (EDeref nopos $ EId nopos "RegExp") [EId nopos "regexp"]))]
  handleThis = ELet nopos [("$this", toString (EId nopos "this"))]


numberPrototype :: ExprPos
numberPrototype = object
  [ ("$proto", EId nopos "@Object_prototype")
  , ("$class", EString nopos "Number")
  , ("$value", ENumber nopos 0)
  , ("constructor", EUndefined nopos) -- Set to Number later
  , ("toString", functionObject ["radix"] $ 
      EIf nopos (eNot (eOr (eStxEq (EId nopos "radix") (EUndefined nopos))
                     (eStxEq (EId nopos "radix") (ENumber nopos 10))))
          (EThrow nopos $ EString nopos "num toStr for non-10 radix NYI")
          (primToStr (getFieldT (EString nopos "$value"))))
  , ("toLocaleString", functionObject [] $ 
      primToStr (getFieldT (EString nopos "$value")))
  , ("valueOf", functionObject [] $ getFieldT (EString nopos "$value"))
  , ("toFixed", functionObject [] $ EString nopos "Number.toFixed")
  , ("toExponential", functionObject ["fracDigs"] $ EString nopos "Number.toExp")
  , ("toPrecision", functionObject ["prec"] $ EString nopos "Number.toPrecision")
  ]


datePrototype :: ExprPos
datePrototype = object
  [ ("$proto", EId nopos "@Object_prototype")
  , ("$class", EString nopos "Date")
  , ("$value", ENumber nopos (0.0/0.0))
  , ("constructor", (EUndefined nopos)) -- Set to Date later
  , ("toString", functionObject [] (EString nopos "THIS IS A DATE"))
  , ("valueOf", functionObject [] (getFieldT (EString nopos "$value")))
  , ("toDateString", functionObject [] $ EString nopos "dateString")
  , ("toTimeString", functionObject [] $ EString nopos "timeString")
  , ("toLocaleString", functionObject [] $ EString nopos "localeString")
  , ("toLocaleDateString", functionObject [] $ EString nopos "localeDateString")
  , ("toLocaleTimeString", functionObject [] $ EString nopos "localeTimeString")
  , ("getTime", functionObject[]$checkThis"Date"$ getFieldT (EString nopos "$value"))
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
  nyi = functionObject [] $ EThrow nopos $ EString nopos "DATE FUNCS NYI"

--errors
--all errors are exactly the same, so these functions actually
--generate an error of a given name.
jsError protname = ERef nopos $ object
  [ ("$proto", EId nopos "@Function_prototype") 
  , ("$class", EString nopos "Function")
  , ("$strRep", EString nopos $ nativeFunctionStrRep "Error")
  , ("length", ENumber nopos 1)
  , ("prototype", EId nopos protname)
  , ("$code", lambda ["msg"] $
    ESeq nopos (setFieldT (EString nopos "$class") (EString nopos "Error"))
             (ESeq nopos (setFieldT (EString nopos "$proto") (EId nopos protname))
               (EIf nopos (eNot (isUndefined (EId nopos "msg")))
                    (setFieldT (EString nopos "message") (toString $ EId nopos "msg"))
                    (EUndefined nopos))))
  ]
errorPrototype name = object
  [ ("$proto", EId nopos "@Object_prototype")
  , ("$class", EString nopos "Error")
  , ("constructor", EUndefined nopos) -- Set to be itself later
  , ("name", EString nopos name)
  , ("message", EString nopos (name ++ " error"))
  , ("toString", functionObject [] $ 
       EOp nopos OStrPlus [toString $ getFieldT (EString nopos "name"),
                           toString $ getFieldT (EString nopos "message")])
  ]


constrNames = 
  ["@Object_prototype", 
   "@Function_prototype", 
   "$Array.prototype", 
   "$String.prototype",
   "$RegExp.prototype", 
   "$Date.prototype", 
   "$Boolean.prototype",
   "$Number.prototype", 
   "$Error.prototype", 
   "$ConversionError.prototype", 
   "$EvalError.prototype", 
   "$RangeError.prototype",
   "$ReferenceError.prototype", 
   "$SyntaxError.prototype", 
   "$TypeError.prototype", 
   "$URIError.prototype"]

setConstructors :: ExprPos
setConstructors = foldr (ESeq nopos) (EUndefined nopos) $ map doit constrNames
 where
  doit name = ESetRef nopos (EId nopos name)
                (EUpdateField nopos (EDeref nopos $ EId nopos name)
                              (EString nopos "constructor")
                              (EDeref nopos $ EId nopos name))
  
ecma262Env :: ExprPos -> ExprPos
ecma262Env body =
  ELet nopos [("$makeException", 
              ELambda nopos ["name", "msg"] $ eNew 
                (EGetField nopos (EDeref nopos $ EId nopos "$global") (EId nopos "name"))
                [EId nopos "msg"])] $
  ELet nopos [("@toPrimitive_String", toPrimitive' "toString" "valueOf")] $
  ELet nopos [("@toPrimitive_Number", toPrimitive' "valueOf" "toString")] $
  updateObject (EId nopos "@Object_prototype") objectPrototypeValues $
  updateObject (EId nopos "@Function_prototype") functionPrototypeValues $
  ELet nopos [("$Date.prototype", ERef nopos datePrototype)] $
  ELet nopos [("$Number.prototype", ERef nopos numberPrototype)] $
  ELet nopos [("$Array.prototype", ERef nopos arrayPrototype)] $
  ELet nopos [("$Boolean.prototype", ERef nopos booleanPrototype)] $

  ELet nopos [("$Error.prototype", ERef nopos (errorPrototype "Error"))] $
  ELet nopos [("$ConversionError.prototype", ERef nopos(errorPrototype "ConversionError"))]$
  ELet nopos [("$EvalError.prototype", ERef nopos (errorPrototype "EvalError"))] $ 
  ELet nopos [("$RangeError.prototype", ERef nopos (errorPrototype "RangeError"))] $ 
  ELet nopos [("$ReferenceError.prototype", ERef nopos (errorPrototype "ReferenceError"))]$
  ELet nopos [("$SyntaxError.prototype", ERef nopos (errorPrototype "SyntaxError"))] $ 
  ELet nopos [("$TypeError.prototype", ERef nopos (errorPrototype "TypeError"))] $ 
  ELet nopos [("$URIError.prototype", ERef nopos (errorPrototype "URIError"))] $ 

  ELet nopos [("Object", ERef nopos jsObject)] $
  ELet nopos [("Function", ERef nopos jsFunction)] $
  ELet nopos [("Array", ERef nopos jsArray)] $
  --regexp.proto uses Array, so it must come after
  ELet nopos [("$RegExp.prototype", ERef nopos regExpPrototype)] $
  ELet nopos [("RegExp", ERef nopos jsRegExp)] $
  ELet nopos [("Date", ERef nopos jsDate)] $
  ELet nopos [("Number", ERef nopos jsNumber)] $
  --string.proto uses RegExp, so it must come after it.
  ELet nopos [("$String.prototype", ERef nopos stringPrototype)] $
  ELet nopos [("String", ERef nopos jsString)] $
  ELet nopos [("Boolean", ERef nopos jsBoolean)] $
  
  ELet nopos [("Error", ERef nopos (jsError "$Error.prototype"))] $ 
  ELet nopos [("ConversionError", ERef nopos (jsError "$ConversionError.prototype"))] $ 
  ELet nopos [("EvalError", ERef nopos (jsError "$EvalError.prototype"))] $ 
  ELet nopos [("RangeError", ERef nopos (jsError "$RangeError.prototype"))] $ 
  ELet nopos [("ReferenceError", ERef nopos (jsError "$ReferenceError.prototype"))] $ 
  ELet nopos [("SyntaxError", ERef nopos (jsError "$SyntaxError.prototype"))] $ 
  ELet nopos [("TypeError", ERef nopos (jsError "$TypeError.prototype"))] $ 
  ELet nopos [("URIError", ERef nopos (jsError "$URIError.prototype"))] $ 
  --if given an object, expects it to be a (ERef (EObject))
  --it itself returns Refs
  ELet nopos [("@toObject", ELambda nopos ["x"] $
    let x = EId nopos "x" in
      EIf nopos (typeIs x "undefined")
          (EThrow nopos $ newError "TypeError" "toObject received undefined") $ 
      EIf nopos (eStxEq x (ENull nopos))
          (EThrow nopos $ newError "TypeError" "toObject received null") $
      EIf nopos (typeIs x "boolean") 
          (ERef nopos $ EObject nopos
            [ ("$proto", EId nopos "$Boolean.prototype")
            , ("$class", EString nopos "Boolean")
            , ("$value", x)]) $ 
      EIf nopos (typeIs x "number")
          (ERef nopos $ EObject nopos
            [ ("$proto", EId nopos "$Number.prototype")
            , ("$class", EString nopos "Number")
            , ("$value", x)]) $ 
      EIf nopos (typeIs x "string")
          (ERef nopos $ EObject nopos
            [ ("$proto", EId nopos "$String.prototype")
            , ("$class", EString nopos "String")
            , ("$value", x)
            , ("length", EOp nopos OStrLen [x])]) $
      x)] $

  ESeq nopos setConstructors $
  updateObject (EId nopos "$global") globalValuesAndFunctions $
  ELet nopos [("this", EId nopos "$global")] $
  body
