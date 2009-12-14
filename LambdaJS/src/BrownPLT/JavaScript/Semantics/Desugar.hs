module BrownPLT.JavaScript.Semantics.Desugar
  ( desugar
  , desugarExpr, desugarExprSetenv
  , desugarStmt
  , desugarStmtsWithResult
  , toString, toNumber, toObject, toBoolean
  , isNumber, isUndefined, isRefComb, isObject, isNull, isLocation
  , primToStr, primToNum
  , applyObj
  , eAnd, eNot, eOr, eStxEq, eNew, eNewDirect, eFor, eArgumentsObj
  , getValue, newError, getGlobalVar
  ) where

import qualified Data.Map as M
import Text.Printf
import Data.Map (Map)
import Data.Maybe (isNothing)
import qualified Data.Set as S
import Data.Set (Set)
import Data.List
import Text.ParserCombinators.Parsec.Pos (SourcePos)
import BrownPLT.JavaScript.Syntax
import BrownPLT.JavaScript.Semantics.Syntax
import BrownPLT.JavaScript.Semantics.LocalVars
import BrownPLT.JavaScript.Semantics.LiftFuncStmts
import BrownPLT.JavaScript.Semantics.DesugarWith
import BrownPLT.JavaScript.Semantics.AssignableVars (assignableVars)

prop :: Prop a -> String
prop p = case p of
  PropId _ (Id _ s) -> s
  PropString _ s -> s
  PropNum _ n -> show n


-- |'True' for JavaScript's logical operators that are guaranteed to produce
-- primitive boolean values.
boolExpr :: Expression a -> Bool
boolExpr e = case e of
  InfixExpr _ op _ _ -> 
    op `elem` [OpLT, OpLEq, OpGT, OpGEq, OpIn, OpInstanceof, OpEq, OpNEq,
               OpNEq, OpStrictEq, OpStrictNEq, OpLAnd, OpLOr]
  PrefixExpr _ PrefixLNot _ -> True
  otherwise -> True
           


getGlobalVar fname = EGetField (EDeref $ EId "$global") (EString fname)


eStxEq :: Expr -> Expr -> Expr
eStxEq e1 e2 = EOp OStrictEq [e1, e2]


--turn 2 boolean exprs into 1 expr that is the or/and
eAnd e1 e2 = EIf e1 e2 (EBool False)
eOr e1 e2 = ELet [("$or", e1)] $ EIf (EId "$or") (EId "$or") e2
eNot e1 = EIf e1 (EBool False) (EBool True)


typeIs :: Expr -> String -> Expr
typeIs e s = eStxEq (EOp OTypeof [e]) (EString s)


--get the base value if it's a reference. 
getValue :: Expr -> Expr
getValue e = ELet [("$x", e)] $
  EIf (typeIs (EId "$x") "location")
      (EDeref (EId "$x"))
      (EId "$x")


isObject e = typeIs e "object"
isLocation e = typeIs e "location"
isLambda e = typeIs e "lambda"
isString e = typeIs e "string"
isPrim e = EOp OIsPrim [e]
isNumber e = typeIs e "number"
isUndefined e = typeIs e "undefined"
isNull e = eStxEq e ENull
isFunctionObj e = ELet [("$isF", e)] $ 
  eAnd (isObject (EId "$isF"))
       (isLambda (EGetField (EId "$isF") (EString "$code")))
--combinator for refs:      
isRefComb f e = eAnd (isLocation e) (f (EDeref e))


primToNum e = EOp OPrimToNum [e]
primToStr e = EOp OPrimToStr [e]
primToBool e = EOp OPrimToBool [e]


--turn a list of expressions into an arguments object
eArgumentsObj :: [Expr] -> Expr -> Expr
eArgumentsObj es callee = EObject (
  [("length", ENumber $ fromIntegral $ length es),
   ("callee", callee),
   ("$class", EString "Object"),
   ("$proto", EId "$Object.prototype"),
   ("$isArgs", EBool True) --used in apply to check correct type
   ] ++
  (map (\ix -> (show ix, (es !! ix))) [0..((length es)-1)]))


--desugar applying an object
applyObj :: Expr -> Expr -> [Expr] -> Expr
applyObj efuncobj ethis es = ELet1 efuncobj $ \x ->
    EApp (EGetField (EDeref $ EId x) (EString "$code")) [ethis, args x]
  where args x = ERef $ ERef $ eArgumentsObj es (EId x)


-- |Algorithm 11.9.6 of ECMA-262, 3rd edition.  OStrictEq accounts for floating
-- point numbers.  Everything else is syntactic equality.
strictEquality :: Expr -> Expr -> Expr
strictEquality =  eStxEq

-- |Algorithm 9.9 of ECMA-262, ed. 3.
--if given an object, expects it to be a (ERef (EObject))
--it itself returns Refs
toObject :: Expr -> Expr
toObject e = 
  ELet1 e $ \x -> 
    EIf (typeIs (EId x) "undefined")
        (EThrow $ newError "TypeError" "toObject received undefined") $        
    EIf (eStxEq (EId x) ENull)
        (EThrow $ newError "TypeError" "toObject received null") $
    EIf (typeIs (EId x) "boolean") 
        (ERef $ EObject
          [ ("$proto", EId "$Boolean.prototype")
          , ("$class", EString "Boolean")
          , ("$value", EId x)]) $ 
    EIf (typeIs (EId x) "number")
        (ERef $ EObject
          [ ("$proto", EId "$Number.prototype")
          , ("$class", EString "Number")
          , ("$value", EId x)]) $ 
    EIf (typeIs (EId x) "string")
        (ERef $ EObject 
          [ ("$proto", EId "$String.prototype")
          , ("$class", EString "String")
          , ("$value", EId x)
          , ("length", EOp OStrLen [EId x])]) $
    (EId x)


-- |According to the specification, toPrimitive may signal a TypeError.
-- this is generalized to do either toString first, or valueOf first,
-- based on the 'hint'
-- Even though GetValue'd values are given to ToPrimitive in ECMA,
-- here we need ERefs because we will apply functions.
-- So make sure you give this ERef (EObject) if you get an object.
-- TODO: Take out the Catastrophes once we know they won't happen
-- just there for debugging for now
toPrimitive_ :: String -> String -> Expr -> Expr
toPrimitive_ first second e = 
  --if it's an object ref, then convert it
  --otherwise it is a primitive, so just return it.
  --catastrophes are a bug with OUR semantics, so they should not be there
  --in the final version - they're just a sanity check.
  ELet [("$x", e)] $ 
    EIf (isLocation (EId "$x"))
        (EIf (eNot (isObject (EDeref (EId "$x"))))
             (EThrow (EString "Catastrophe - toPrim given a ref of a not-obj"))
             cvt)
        (EIf (isObject (EId "$x"))
             (EThrow (EString "Catastrophe - toPrim given plain object"))
             (EId "$x"))
  -- [[DefaultValue]] (8.6.2.6)
  where 
    --if valueOf is a function, try it. else try tostr.
    cvt = ELet [("$vOf", (EGetField (EDeref (EId "$x")) (EString first)))] $    
            EIf (isRefComb isFunctionObj (EId "$vOf"))
              (ELet [("$vRes", applyObj (EId "$vOf") (EId "$x") [])] $
                EIf (isPrim (EId "$vRes"))
                    (EId "$vRes")
                    str)
              str
    --if toString is a function, try it. else throw excp
    str = ELet [("$toStr", (EGetField (EDeref (EId "$x")) (EString second)))] $
            EIf (isRefComb isFunctionObj (EId "$toStr"))
              (ELet [("$tRes", applyObj (EId "$toStr") (EId "$x") [])] $
                EIf (isPrim (EId "$tRes"))
                    (EId "$tRes")
                    exc)
              exc
    exc = (EThrow $ newError "TypeError" "cannot convert obj to primitive")


toPrimitive_String = toPrimitive_ "toString" "valueOf"
toPrimitive_Number = toPrimitive_ "valueOf" "toString"
toPrimitive = toPrimitive_Number


--ECMA 9.3
--once again, must get object refs to pass them in as 'this' in toPrimitive
toNumber :: Expr -> Expr
toNumber e = 
  ELet [("$toNum", e)] $
    EIf (isLocation (EId "$toNum"))
        (EIf (eNot (isObject (EDeref (EId "$toNum"))))
             (EThrow (EString "Catastrophe - toNum given a ref of a not-obj"))
             (primToNum $ toPrimitive_Number (EId "$toNum")))
        (EIf (isObject (EId "$toNum"))
             (EThrow (EString "Catastrophe - toNum given plain object"))
             (primToNum (EId "$toNum")))


toBoolean = primToBool


-- |Algorithm 9.8
-- expects objects to be locations to be able to call toPrimitive.
-- otherwise it should be a value.
toString :: Expr -> Expr
toString e =
  ELet [("$toStr", e)] $
    EIf (isLocation (EId "$toStr"))
        (EIf (eNot (isObject (EDeref (EId "$toStr"))))
             (EThrow (EString "Catastrophe - toStr given a ref of a not-obj"))
             (primToStr $ toPrimitive (EId "$toStr")))
        (EIf (isObject (EId "$toStr"))
             (EThrow (EString "Catastrophe - toStr given plain object"))
             (primToStr (EId "$toStr")))


abstractEquality :: Expr -> Expr -> Expr
abstractEquality e1 e2 = ELet [("$lhs", e1), ("$rhs", e2)] $
  EIf (EOp OAbstractEq [EId "$lhs", EId "$rhs"]) 
      (EBool True) $
  EIf (isLocation (EId "$lhs"))
      (EOp OAbstractEq [toPrimitive (EId "$lhs"), EId "$rhs"]) $
  EIf (isLocation (EId "$rhs"))
      (EOp OAbstractEq [EId "$lhs", toPrimitive (EId "$rhs")])
      (EBool False)



      
--(in order of appearance in the spec)
infixOp :: InfixOp -> Expr -> Expr -> Expr
infixOp op e1 e2 = case op of
  --ECMA 11.5. 
  OpMul -> o OMul
  OpDiv -> o ODiv
  OpMod -> o OMod
  
  --ECMA 11.6.1, preserve order of operations
  OpAdd -> 
    binds e1 e2 $ 
      -- In our paper, we state that
      --   desugar[[e1 + e2]] = let (x = desugar[[e1]], y = desugar[[e2]]) ...
      -- This isn't quite the case, but in toPrimitive, desugar[[e1]] and
      -- desugar[[e2]] are let-bound, so it's more like:
      --   desugar[[e1 + e2]] = let (x = let (obj = desugar[[e1]]) ..., 
      --                             y = let (obj = desugar[[e2]]) ...) ...
      -- which can still be expressed as a two-holed context.
      ELet [("$addLhs", toPrimitive (EId "$opLhs")),
            ("$addRhs", toPrimitive (EId "$opRhs"))] $
        EIf (eOr (typeIs (EId "$addLhs") "string")
                 (typeIs (EId "$addRhs") "string"))
            --we can use prim->str and prim->num here instead
            --of toString/toNumber because the exprs are already
            --converted to primitives.
            (EOp OStrPlus [primToStr $ EId "$addLhs",
                           primToStr $ EId "$addRhs"])
            (EOp ONumPlus [primToNum $ EId "$addLhs", 
                           primToNum $ EId "$addRhs"])  
  OpSub -> o OSub --11.6.2
  
  OpLShift -> shift OLShift 
  OpSpRShift -> shift OSpRShift
  OpZfRShift -> shift OZfRShift
    
  OpLT -> binds e1 e2 $ checkLtGt $ lt (EId "$opLhs") (EId "$opRhs")
  OpGT -> binds e1 e2 $ checkLtGt $ lt (EId "$opRhs") (EId "$opLhs") 
  OpLEq -> binds e1 e2 $ checkLeqGeq $ lt (EId "$opRhs") (EId "$opLhs")
  OpGEq -> binds e1 e2 $ checkLeqGeq $ lt (EId "$opLhs") (EId "$opRhs") 

  --11.8.6, 15.3.5.3
  OpInstanceof -> ELet [("$lhs", e1), ("$rhs", e2)] $
    EIf (eNot (isRefComb isFunctionObj (EId "$rhs"))) 
      (EThrow $ newError "TypeError" "instanceof args of wrong type") $
      EIf (eNot $ isRefComb isObject (EId "$lhs")) (EBool False) $
        ELet1 (EGetField (EDeref$EId "$rhs") (EString "prototype")) $ \fProt ->
        ELet2 (ERef $ EId "$lhs") (ERef (EBool False))$ \curLHS res ->
          ESeq 
            (ELabel "$break" $ 
              --while the curLHS isn't null:
              EWhile (eNot $ isNull (EDeref $ EId curLHS)) $
                --if it matches the rhs.prototype, we're done
                EIf (eStxEq (EDeref $ EId curLHS) (EId fProt))
                 (ESeq (ESetRef (EId res) (EBool True))
                       (EBreak "$break" EUndefined))
                 --otherwise go up once the prototype chain
                 (ESetRef (EId curLHS) (EGetField (EDeref $EDeref $ EId curLHS) 
                                                  (EString "$proto"))))
            (EDeref $ EId res)

  OpIn -> ELet2 (toString e1) (toObject e2) $ \fieldId objId -> 
    EOp OHasOwnProp [EDeref $ EId objId, EId fieldId]
  OpEq -> abstractEquality e1 e2
  OpNEq -> eNot $ abstractEquality e1 e2
  OpStrictEq -> strictEquality e1 e2
  OpStrictNEq -> eNot $ strictEquality e1 e2

  OpBAnd -> bitop OBAnd
  OpBXor -> bitop OBXOr
  OpBOr  -> bitop OBOr
  
  --note: i think their "GetValue" is our equivalent
  --of "VarRef".? for example, if you have:
  --a && b
  --you don't want b to be reduced to an (object), because if you
  --do: print(a&&b), b must be a ref to to the tostring conv. properly.
  OpLAnd -> 
    ELet [("$lAnd", e1)] $
      EIf (eNot $ toBoolean (EId "$lAnd"))
          (EId "$lAnd")
          e2
  OpLOr -> 
    ELet [("$lOr", e1)] $
      EIf (toBoolean (EId "$lOr"))
          (EId "$lOr")
          e2
    
  where 
    --steps 1-4 of the algs
    binds l r e =
      ELet [("$opLhs", l),
            ("$opRhs", r)] e
    --bit-shifts (11.7.1) 
    shift eop =
      binds e1 e2 $ 
        --toint32 only takes numbers, so must do that here:
        ELet [("$lhsShift", EOp OToInt32 [toNumber (EId "$opLhs")]),
              ("$rhsShift", EOp OToUInt32 [toNumber (EId "$opRhs")])] $
          ELet [("$rhsShift2", EOp OBAnd [EId "$rhsShift", 
                                          --OToInteger is a technical
                                          --workaround to make sure we have
                                          --a plain integer in the Scheme
                                          EOp OToInteger [ENumber 0x1F]])] $
            (EOp eop [EId "$lhsShift", EId "$rhsShift2"])
    -- *, -, /, etc
    o eop = 
      binds e1 e2 $ 
        ELet [("$opLhs2", toNumber (EId "$opLhs")),
              ("$opRhs2", toNumber (EId "$opRhs"))] $
          EOp eop [EId "$opLhs2", EId "$opRhs2"]
    --alg 11.8.5
    lt e1 e2 = 
      ELet [("$ltLhs", toPrimitive e1),
            ("$ltRhs", toPrimitive e2)] $
        EIf (eAnd (typeIs (EId "$ltLhs") "string")
                  (typeIs (EId "$ltRhs") "string"))
            (EOp OStrLt [EId "$ltLhs", EId "$ltRhs"])
            (EOp OLt    [primToNum $ EId "$ltLhs", 
                         primToNum $ EId "$ltRhs"])
    --step 6 of <, >
    checkLtGt e =
      ELet [("$res", e)] $
        EIf (typeIs (EId "$res") "undefined")
            (EBool False)
            (EId "$res")
    --step 6 of <=, >= 
    checkLeqGeq e = 
      ELet [("$res", e)] $
        EIf (eOr (typeIs (EId "$res") "undefined")
                 (EId "$res"))
            (EBool False)
            (EBool True)
    bitop eop = 
      binds e1 e2 $ 
        ELet [("$bitLhs", EOp OToInt32 [toNumber (EId "$opLhs")]),
              ("$bitRhs", EOp OToInt32 [toNumber (EId "$opRhs")])] $
          EOp eop [EId "$bitLhs", EId "$bitRhs"]
                      

 

prefixOp :: PrefixOp -> Expr -> Expr
prefixOp op e = case op of 
  -- It is strange that that the subterm of delete is an expression and not
  -- an l-value.  Note that that delete has no effect when its subexpression
  -- is not l-value like.
  PrefixDelete -> case e of
    EGetField (EDeref eObj) eString ->
      ELet [("$delObj", eObj),
            ("$delStr", eString)] $
        EIf (EOp OObjCanDelete [EDeref $ EId "$delObj", EId "$delStr"])
            (ESeq 
              (ESetRef (EId "$delObj")
                (EDeleteField (EDeref $ EId "$delObj") (EId "$delStr")))
              (EBool True))
            (EBool False)
    otherwise -> EBool True
    
  PrefixVoid -> ESeq (getValue e) EUndefined
  --TODO: make sure step 3 in 11.4.3 makes sense for our typeof:
  PrefixTypeof -> EOp OSurfaceTypeof [getValue e]
  PrefixBNot -> EOp OBNot [EOp OToInt32 [toNumber e]]
  PrefixLNot -> eNot (toBoolean e)
  PrefixPlus -> toNumber e
  PrefixMinus -> EOp OSub [ENumber 0.0, toNumber e]


type Env = M.Map Ident Bool


--i swear this is what 15.4 says:
isArrayIndex e = 
  ELet [("$isai", e)] $
    eAnd (isString (EId "$isai"))
         (ELet [("$intai", EOp OToUInt32 [primToNum $ EId "$isai"])] $
           (eAnd (eNot (eStxEq (EId "$intai") (ENumber 0xFFFFFFFF)))
                 (eStxEq (primToStr (EId "$intai")) (EId "$isai"))))


--helper since it's used in stmt too:
eAssignLVar :: Env -> String -> Expr -> Expr
eAssignLVar env x e = case M.lookup x env of
  Just True -> ESetRef (EId x) e
  Nothing -> ESetRef (EId "$global") 
                     (EUpdateField (EDeref $ EId "$global")
                                   (EString x)
                                   e)
  Just False -> error "eAssignLVar: assigning a non-assignable variable"

eVarRef :: Env -> String -> Expr
eVarRef env x = case M.lookup x env of
  Just True -> EDeref (EId x)
  Just False -> EId x
  Nothing -> getGlobalVar x


--takes our expressions, writes out a new
--this takes in an arguments obj directly. used from String.split.
eNewDirect :: Expr -> Expr -> Expr
eNewDirect eConstr argumentObj = 
  ELet [("$constr", eConstr)] $
    EIf (eNot $ isRefComb isFunctionObj (EId "$constr"))
        (EThrow $ newError "TypeError" "new not given function") $
        newWork eConstr argumentObj 
  where --newWork split up here so that we don't have infinite recursion
    newWork eConstr argumentObj = 
        --[[Construct]], 13.2.2 . it's always the same,
        --so no need to have it be a $constr field (like $call)
         (ELet [("$protoField", 
                EGetField (EDeref (EId "$constr")) (EString "prototype"))] $
          ELet [("$protoObj",
                 EIf (isRefComb isObject (EId "$protoField"))
                     (EId "$protoField")
                     (EId "$Object.prototype"))] $
            ELet [("$newObj", 
                   ERef $ EObject [("$constructing", EBool True),
                                   ("$class", EString "Object"),
                                   ("$proto", EId "$protoField")])] $
              ELet1 (EApp (EGetField (EDeref (EId "$constr"))(EString "$code"))
                         [EId "$newObj", argumentObj]) $ \newResult ->
                EIf (isRefComb isObject (EId newResult))
                    (EId newResult)
                    (ESeq (ESetRef (EId "$newObj")
                      (EDeleteField (EDeref $ EId "$newObj")
                                    (EString "$constructing")))
                      (EId "$newObj")))

--this is the traditional list of exprs one:
eNew eConstr es = ELet1 eConstr $ \c ->
  eNewDirect (EId c) (ERef $ ERef $ eArgumentsObj es (EId c))
newError name msg = 
  EApp (EId "$makeException") [EString name, EString (":" ++ msg)]




--for loop using our expressions. test better evaluate to a boolean!
--sets up the break/continue as well.
-- ForStmt _ init incr test body -> eFor (forInit env init) (maybeExpr env incr)
--    (toBoolean $ maybeExpr env test) (stmt env body)  

eFor init incr test body = ESeq init loop
 where loop = ELabel "$break" $
                EWhile test (ESeq body' incr)
       body' = ELabel "$continue" body



-- |Evaluate and lvalue, bind it to an identifier, pass the identifier to
-- 'bodyFn'.  'bodyFn' also receives a setter for the lvalue.
-- The setter manages various JavaScript details, including:
-- 11.2.1 (eval LHS), 11.13.1 (assignop), 8.7.2 (putValue), and 
-- 8.6.2.2 (Object put) and 15.4.5.1 (Array put).
theSetter :: Ident -> Ident -> (Expr -> Expr)
theSetter objRef fieldRef = \v -> ELet1 v $ \vId -> 
  ESeq (EIf (eStxEq (EGetField (EDeref (EId objRef)) (EString "$class"))
                    (EString "Array"))
         (setArray objRef fieldRef (EId vId))
         (setObj objRef fieldRef (EId vId)))
       (EId vId)
  where setObj objRef field v = 
          ESetRef (EId objRef) 
                  (EUpdateField (EDeref (EId objRef)) (EId field) v)
        setArray objRef field v = 
          --15.4.5.1:
          EIf (eStxEq (EId field) (EString "length"))
              (EThrow (EString "setting .length of array NYI")) $
              ELet1 (setObj objRef field v) $ \r ->
                 --steps 7-11
               EIf (isArrayIndex (EId field))
                  (ELet [("$aindx", primToNum $ EId field),
                         ("$curln", EGetField (EDeref (EId objRef))
                                              (EString "length"))] $
                    EIf (EOp OLt [EId "$aindx", EId "$curln"])
                       (EId r)
                       (ESeq
                          (ESetRef 
                            (EId objRef)
                            (EUpdateField (EDeref (EId objRef))
                                          (EString "length")
                                          (EOp ONumPlus [EId "$aindx",
                                                         ENumber 1])))
                          (EId r)))
                  (EId r)

withLValue :: Env 
           -> LValue SourcePos  
           -> (Expr -> (Expr -> Expr) ->  Expr) -- ^getter, setter
           -> Expr
withLValue env (LVar _ x) bodyFn = case M.lookup x env of
  Just True -> 
    bodyFn (EDeref (EId x)) 
            (\v -> ESeq (ESetRef (EId x) v) (EDeref (EId x)))
  Nothing ->
    bodyFn (getGlobalVar x) $ \v ->
               EGetField 
                 (EDeref
                   (ESetRef (EId "$global")
                            (EUpdateField (EDeref (EId "$global"))
                                          (EString x) v)))
                 (EString x)
  Just False -> error "withLValue applied to a non-assignable value"
withLValue env (LDot _ e x) bodyFn =
  ELet2 (expr env e) (EString x) $ \objRef field ->
    bodyFn (EGetField (EDeref (EId objRef)) (EString x))
           (theSetter objRef field)
withLValue env (LBracket _ e1 e2) bodyFn =
  ELet2 (expr env e1) (toString (expr env e2)) $ \objRef field ->
    bodyFn (EGetField (EDeref (EId objRef)) (EId field))
           (theSetter objRef field)



expr :: Env -> Expression SourcePos -> Expr
expr env e = case e of
  StringLit _ s -> EString s
  RegexpLit p s glob ci -> 
    eNew (EDeref $ EId "RegExp") [ --EId since we want the original one
      EString s, EString ((if glob then "g" else "") ++
                          (if ci   then "i" else ""))]
  --ArrayLit more or less follows 11.1.4 but does some things
  --more directly.
  ArrayLit _ es -> 
    ERef (EObject ([ ("$class", EString "Array")
                   , ("$proto", EId "$Array.prototype")
                   , ("length", ENumber (fromIntegral $ length es)) ]
                   ++ 
                   (map (\ix -> (show ix, expr env (es!!ix))) 
                        [0..((length es)-1)])
                   ))
  NumLit _ n -> ENumber n
  IntLit _ n -> ENumber (fromIntegral n)
  BoolLit _ b -> EBool b
  NullLit _ -> ENull
  ObjectLit _ ps -> ERef $ EObject $ 
    proto:("$class", EString "Object"):
      (map (\(p,e') -> (prop p, expr env e')) ps)
      where proto = ("$proto", EId "$Object.prototype")
  ThisRef _ -> EId "this" 
  VarRef _ (Id _ s) -> eVarRef env s
  -- PrefixDelete assumes that DotRef and BracketRef are desugared to iimmediate
  -- EGetField expressions.
  DotRef _ e (Id _ s) -> EGetField (EDeref $ toObject $ expr env e) 
                                   (EString s)
  BracketRef _ e1 e2 -> 
    EGetField (EDeref $ toObject $ expr env e1) (toString $ expr env e2)
  NewExpr _ eConstr es -> eNew (expr env eConstr) (map (expr env) es)
  PrefixExpr _ op e -> prefixOp op (expr env e)
  UnaryAssignExpr _ op lv -> withLValue env lv $ \get setter -> case op of
    PostfixInc -> ELet1 get $ \x -> 
      ESeq (setter $ EOp ONumPlus [ENumber 1, toNumber (EId x)])
           (EId x)
    PostfixDec -> ELet1 get $ \x -> 
      ESeq (setter $ EOp ONumPlus [toNumber (EId x), ENumber (-1)])
           (EId x)
    PrefixInc -> 
      ELet1 (EOp ONumPlus [toNumber get, ENumber 1]) $ \v -> setter (EId v)
    PrefixDec -> 
      ELet1 (EOp ONumPlus [toNumber get, ENumber (-1)]) $ \v -> setter (EId v)
  -- typeof e === string-constant is a common pattern that we desugar to
  -- something simpler, when we aren't checking for "object" or "function".
  InfixExpr _ OpStrictEq (PrefixExpr _ PrefixTypeof e) (StringLit _ s)
    | s /= "function" && s /= "object" ->
    EOp OStrictEq [EOp OTypeof [expr env e], EString s]
  InfixExpr _ op e1 e2 -> infixOp op (expr env e1) (expr env e2)
  CondExpr _ e1 e2 e3 -> EIf (toBoolean $ expr env e1) 
                             (expr env e2) (expr env e3)
  AssignExpr _ OpAssign lv e -> withLValue env lv $ \get setter ->
    setter (expr env e)
  AssignExpr p op lv e -> 
    expr env (AssignExpr p OpAssign lv (InfixExpr p iOp lvAsR e))
   where
    iOp = case op of
      OpAssignAdd -> OpAdd
      OpAssignSub -> OpSub
      OpAssignMul -> OpMul
      OpAssignDiv -> OpDiv
      OpAssignMod -> OpMod
      OpAssignLShift -> OpLShift
      OpAssignSpRShift -> OpSpRShift
      OpAssignZfRShift -> OpZfRShift
      OpAssignBAnd -> OpBAnd
      OpAssignBXor -> OpBXor
      OpAssignBOr -> OpBOr
      OpAssign -> error "Haskell has gone haywire."
    lvAsR = case lv of
      LVar p x -> VarRef p (Id p x)
      LDot p e1 field -> DotRef p e1 (Id p field)
      LBracket p e1 e2 -> BracketRef p e1 e2
  ParenExpr _ e1 -> expr env e1
  ListExpr _ [] -> error "Desugar.hs: expr got empty ListExpr"
  ListExpr _ [e'] -> expr env e'
  ListExpr a (e':es) -> ESeq (expr env e') (expr env (ListExpr a es))
  CallExpr _ (DotRef _ obj (Id _ method)) args ->
    ELet [("$obj", toObject $ expr env obj)] $
      applyObj (EGetField (EDeref $ EId "$obj") (EString method)) (EId "$obj")
               (map (expr env) args)          
  CallExpr _ e es -> 
    ELet [("$obj", expr env e)] $
      EIf (eNot (isRefComb isFunctionObj (EId "$obj")))
          (EThrow $ newError "TypeError" "CallExpr given non-function")
          (applyObj (EId "$obj") (EId "$global") (map (expr env) es))
  --TODO: don't just ignore mname                            
  FuncExpr p mname ids unliftedStmt -> 
    ERef $ EObject [("$code", code), 
                    ("arguments", arguments),
                    ("prototype", prototype),
                    ("$strRep", EString strRep),
                    ("$proto", EId "$Function.prototype")]
      where s = BlockStmt p (liftFuncStmts [unliftedStmt])
            arg x ix = case x `S.member` assignableArgs of
              True -> ERef $ EGetField (EDeref $ EDeref (EId "arguments"))
                                       (EString $ show ix)
              False -> EGetField (EDeref $ EDeref (EId "arguments"))
                                 (EString $ show ix)
            --cascade the lets in formals so that the rightmost one
            --is the one remaining
            --
            formals' = map (\(x, ix) -> (unId x, arg (unId x) ix)) 
                           (zip ids [0..])
            formals rest = foldr f rest formals'
            f bind rest = ELet [bind] rest
            code = ELambda ["this", "arguments"] $ 
                     formals $ 
                     ELet locals $
                       ELabel "$return" (stmt env' s)
            prototype = ERef $ EObject [("$proto", EId "$Object.prototype"),
                                        ("$class", EString "Object")]
            arguments = ENull
            vars = localVars s
            locals = map (\x -> (x, ERef EUndefined)) vars
            argSet = S.fromList (map unId ids)
            assignable = assignableVars unliftedStmt
            assignableArgs = argSet `S.intersection` assignable
            pureArgs = argSet `S.difference` assignableArgs
            env' = M.unions $
                     [ M.fromList $ zip vars (repeat True)
                     , M.fromList $ zip (S.toList pureArgs) (repeat False)
                     , M.fromList $ zip (S.toList assignableArgs) (repeat True)
                     , M.fromList [("arguments", True), ("this", True)]
                     , env
                     ]          
            strRep = printf "function %s(%s) {\n    [cant look here]\n}"
                       (maybe "" unId mname) strArgs
            strArgs = concat $ intersperse "," (map unId ids)


maybeExpr :: Env -> Maybe (Expression SourcePos) -> Expr
maybeExpr _ Nothing = EUndefined
maybeExpr env (Just e) = expr env e

--{var x = 20; var x;} should have x be 20.
varDecl :: Env -> VarDecl SourcePos -> Expr
varDecl env (VarDecl p (Id _ x) rhs) = case M.lookup x env of
    --True: it's a local var. if no declaration, don't do anything.
    Just True -> if (isNothing rhs) then EUndefined else ESetRef (EId x) e
    -- It's global. if it exists, do nothing, else set to undefined.
    Nothing -> 
      if (isNothing rhs)
        then EIf (EOp OHasOwnProp [EDeref $ EId "$global", EString x])
                 EUndefined setglob
        else setglob
    Just False -> error "varDecl of a non-assignable variable"
                 
  where e = case rhs of
              Nothing -> EUndefined
              Just e' -> expr env e'                                   
        setglob = ESetRef (EId "$global") 
                   (EUpdateField (EDeref $ EId "$global")
                                 (EString x) e)


forInit :: Env -> ForInit SourcePos -> Expr
forInit _ NoInit = EUndefined
forInit env (VarInit decls) = foldr ESeq EUndefined (map (varDecl env) decls)
forInit env (ExprInit e) = expr env e


catchClause :: Env -> CatchClause SourcePos -> Expr
catchClause env (CatchClause _ (Id _ x) s) = ELambda [x] $
  ELet [(x, ERef (EId x))] (stmt env' s)
  where env' = M.insert x True env


caseClauses :: Ident -> Ident -> Env -> CaseClause SourcePos -> Expr -> Expr
caseClauses testId caseId env (CaseClause _ e ss) remainingCases = 
  ELet [(testId, EIf (EId testId)
                      (EBool True) 
                      (EOp OStrictEq [EId caseId, expr env e]))] $
    ESeq
      (EIf (EId testId)
           (foldr (\s e -> ESeq (stmt env s) e) EUndefined ss)
           EUndefined)
      remainingCases
caseClauses _ _ env (CaseDefault _ ss) innerExpr =
   foldr (\s e -> ESeq (stmt env s) e) innerExpr ss


stmt :: Env -> Statement SourcePos -> Expr
stmt env s = case s of
  BlockStmt _ [] -> EUndefined
  BlockStmt a (s:ss) -> ESeq (stmt env s) (stmt env (BlockStmt a ss))
  EmptyStmt _ -> EUndefined
  ExprStmt _ e -> expr env e
  IfStmt _ e s1 s2 -> case boolExpr e of
    True -> EIf (expr env e) (stmt env s1) (stmt env s2)
    False -> EIf (toBoolean $ expr env e) (stmt env s1) (stmt env s2)
  IfSingleStmt _ e s1 -> EIf (toBoolean $ expr env e) 
                             (stmt env s1)
                             EUndefined
  WhileStmt _ e1 s1 -> 
    ELabel "$break" $
      EWhile (toBoolean $ expr env e1) $
        ELabel "$continue" 
          (stmt env s1)
  ForStmt _ init test incr body -> 
    eFor (forInit env init) (maybeExpr env incr)
         (toBoolean $ maybeExpr env test) (stmt env body)
  ThrowStmt _ e -> EThrow (expr env e)
  TryStmt _ body catches finally -> 
    EFinally withoutFinally (maybeStmt env finally)
      where withoutFinally = 
              foldl (\body catch -> ECatch body (catchClause env catch)) 
                    (stmt env body)
                    catches
  BreakStmt _ Nothing -> EBreak "$break" EUndefined
  BreakStmt _ (Just (Id _ lbl)) -> EBreak lbl EUndefined
  ContinueStmt _ Nothing -> EBreak "$continue" EUndefined
  ContinueStmt _ (Just (Id _ lbl)) -> EBreak lbl EUndefined
  LabelledStmt _ (Id _ lbl) s1 -> ELabel lbl (stmt env s1)
  ReturnStmt _ Nothing -> EBreak "$return" EUndefined
  ReturnStmt _ (Just e) -> EBreak "$return" (expr env e)
  VarDeclStmt _ decls -> foldr ESeq EUndefined (map (varDecl env) decls)
  FunctionStmt p _ _ _ -> 
    error $ "Desugar.hs : expected FunctionStmt at " ++ show p
  WithStmt _ obj body -> desugarWith (toObject $ expr env obj) (stmt env body)
  ForInStmt _ (ForInVar (Id p x)) e s -> forin p x e s
  ForInStmt _ (ForInNoVar (Id p x)) e s -> forin p x e s
  DoWhileStmt _ _ _ -> nyi "DoWhileStmt"
  SwitchStmt p e cases ->
    ELet1 (expr env e) $ \caseId ->
      ELabel "$break" $
        ELet1 (EBool False) $ \testId ->
        foldr (caseClauses testId caseId env) EUndefined cases
 where
  nyi s = error $ "Desugar.hs: " ++ s
  --TODO eventually: fix to work with any lhs
  forin p x eObj body = 
    ELet [("$_finObj", expr env eObj),
          ("$finIter", ERef $ EUndefined)] $ --internal iterator
      --ECMA-breaking change: iterating thru undefined doesn't throw typeerr
      EIf (eOr (isUndefined (EId "$_finObj"))
               (eStxEq (EId "$_finObj") ENull))
          EUndefined $
          restfin p x body
  restfin p x body =    
    ELet [("$finObj", toObject $ EId "$_finObj")] $
      ELabel "$break" $
        --while there is a next:
        EWhile (EOp OObjIterHasNext [EDeref $ EId "$finObj", 
                                     EDeref $ EId "$finIter"]) $
          (ELabel "$continue" $
             --update our iterator
             ESeq (ESetRef (EId "$finIter")
                           (EOp OObjIterNext [EDeref $ EId "$finObj",
                                              EDeref $ EId "$finIter"]))$
               --get the value into the lvar and eval the body
               ELet [("$curval", (EOp OObjIterKey [EDeref $ EId "$finObj", 
                                        EDeref$EId"$finIter"]))] $
                 --faking DontEnum: dont enum $ properties.
                 EIf (EOp OStrStartsWith [EId "$curval", EString "$"])
                     EUndefined
                     (ESeq (eAssignLVar env x (EId "$curval"))
                           (stmt env body)))
          --if someone continues, it'll go into the while, and the
          --right thing should happen.


maybeStmt :: Env -> Maybe (Statement SourcePos) -> Expr
maybeStmt _ Nothing = EUndefined
maybeStmt env (Just s) = stmt env s


desugarExpr :: Expression SourcePos -> (Expr -> Expr) -> Expr
desugarExpr e env = env (expr M.empty e)


desugarStmt :: Statement SourcePos -> (Expr -> Expr) -> Expr
desugarStmt s env = env (stmt M.empty s)


desugarExprSetenv :: Expression SourcePos -> Env -> Expr
desugarExprSetenv e env = expr env e


-- |Desugar a sequence of statements, in the given environment.  Instead of
-- producing EUndefined, the result of the sequence of statements is the
-- 'result' parameter.
desugarStmtsWithResult :: [Statement SourcePos] 
                       -> (Expr -> Expr) -> Expr -> Expr
desugarStmtsWithResult stmts env result = 
  env $ foldr ESeq result (map (stmt M.empty) stmts')
          where stmts' = liftFuncStmts stmts


desugar :: JavaScript SourcePos -> (Expr -> Expr) -> Expr
desugar (Script _ ss) env = 
  desugarStmtsWithResult ss env EUndefined