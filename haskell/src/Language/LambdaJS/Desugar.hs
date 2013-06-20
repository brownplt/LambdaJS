module Language.LambdaJS.Desugar
  ( desugar
  , desugarExpr
  , desugarStmt
  , desugarStmtsWithResult
  , toString, toNumber, toObject, toBoolean
  , isNumber, isUndefined, isRefComb, isObject, isNull, isLocation
  , isFunctionObj
  , primToStr, primToNum, toPrimitive, strictEquality
  , toPrimitive_Number
  , applyObj
  , eAnd, eNot, eOr, eNew, eNewDirect, eFor, eArgumentsObj
  , getValue, newError, getGlobalVar
  , typeIs, isArrayIndex
  ) where

import qualified Data.Map as M
import Text.Printf
import Data.Map (Map)
import Data.Maybe (isNothing)
import qualified Data.Set as S
import Data.Set (Set)
import Data.List
import Text.ParserCombinators.Parsec.Pos (SourcePos)
import Language.ECMAScript3.Syntax
import Language.LambdaJS.Syntax
import Language.LambdaJS.LocalVars
import Language.LambdaJS.LiftFuncStmts
import Language.LambdaJS.DesugarWith
import Language.LambdaJS.AssignableVars (assignableVars)

prop :: Prop a -> String
prop p = case p of
  PropId _ (Id _ s) -> s
  PropString _ s -> s
  PropNum _ n -> show n


-- |'True' for JavaScript's logical operators that are guaranteed to produce
-- primitive boolean values.
boolExpr :: Expression a -> Bool
boolExpr e = case e of
  InfixExpr a op _ _ -> 
    op `elem` [OpLT, OpLEq, OpGT, OpGEq, OpIn, OpInstanceof, OpEq, OpNEq,
               OpNEq, OpStrictEq, OpStrictNEq, OpLAnd, OpLOr]
  PrefixExpr a PrefixLNot _ -> True
  otherwise -> True
           

getGlobalVar fname = EGetField nopos (EDeref nopos $ EId nopos "$global") (EString nopos fname)

--turn 2 boolean exprs into 1 expr that is the or/and
eAnd e1 e2 = EIf nopos e1 e2 (EBool nopos False)
eOr e1 e2 = ELet nopos [("$or", e1)] $ EIf nopos (EId nopos "$or") (EId nopos "$or") e2
eNot e1 = EIf nopos e1 (EBool nopos False) (EBool nopos True)


typeIs :: ExprPos -> String -> ExprPos
typeIs e s = strictEquality (EOp nopos OTypeof [e]) (EString nopos s)


--get the base value if it's a reference. 
getValue :: ExprPos -> ExprPos
getValue e = ELet nopos [("$x", e)] $
  EIf nopos (typeIs (EId nopos "$x") "location")
      (EDeref nopos (EId nopos "$x"))
      (EId nopos "$x")


isObject e = typeIs e "object"
isLocation e = typeIs e "location"
isLambda e = typeIs e "lambda"
isString e = typeIs e "string"
isNumber e = typeIs e "number"
isUndefined e = typeIs e "undefined"
isNull e = strictEquality e (ENull nopos)
isFunctionObj e = ELet nopos [("$isF", e)] $ 
  eAnd (isObject (EId nopos "$isF"))
       (isLambda (EGetField nopos (EId nopos "$isF") (EString nopos "$code")))
--combinator for refs:      
isRefComb f e = 
  EApp nopos (EId nopos "@isRefComb") 
    [ELambda nopos ["@x"] (f (EId nopos "@x")), e]


primToNum e = EOp (label e) OPrimToNum [e]
primToStr e = EOp (label e) OPrimToStr [e]
primToBool e = EOp (label e) OPrimToBool [e]


--turn a list of expressions into an arguments object
eArgumentsObj :: [ExprPos] -> ExprPos -> ExprPos
eArgumentsObj es callee = EObject  nopos (
  [("length", ENumber nopos $ fromIntegral $ length es),
   ("callee", callee),
   ("$class", EString nopos "Object"),
   ("$proto", EId nopos "@Object_prototype"),
   ("$isArgs", EBool nopos True) --used in apply to check correct type
   ] ++
  (map (\ix -> (show ix, (es !! ix))) [0..((length es)-1)]))


--desugar applying an object
applyObj :: ExprPos -> ExprPos -> [ExprPos] -> ExprPos
applyObj efuncobj ethis es = ELet1 nopos efuncobj $ \x ->
    EApp (label efuncobj) (EGetField (label ethis) (EDeref nopos $ EId nopos x) (EString nopos "$code")) [ethis, args x]
  where args x = ERef nopos $ ERef nopos $ eArgumentsObj es (EId nopos x)


strictEquality e1 e2 = EOp nopos OStrictEq [e1, e2] -- Algorithm 11.9.6 
toObject e = EApp nopos (EId nopos "@toObject") [e]
toPrimitive_String e = EApp nopos (EId nopos "@toPrimitive_String") [e]
toPrimitive_Number e = EApp nopos (EId nopos "@toPrimitive_Number") [e]
toPrimitive = toPrimitive_Number
toNumber e = EApp nopos (EId nopos "@toNumber") [e]
toBoolean = primToBool

-- |Algorithm 9.8
-- expects objects to be locations to be able to call toPrimitive.
-- otherwise it should be a value.
toString :: ExprPos -> ExprPos
toString e =
  ELet nopos [("$toStr", e)] $
    EIf nopos (isLocation (EId nopos "$toStr"))
        (primToStr $ toPrimitive (EId nopos "$toStr"))
        (primToStr (EId nopos "$toStr"))

infixOp op e1 e2 = EApp nopos (EId nopos ("@" ++ show op)) [e1, e2]

prefixOp op e = case op of
  PrefixDelete -> case e of
    EGetField a1 (EDeref a2 eObj) eString ->
      EApp nopos (EId nopos "@delete") [eObj, eString]
    otherwise -> EBool nopos True
  otherwise -> EApp nopos (EId nopos ("@" ++ show op)) [e]

type Env = M.Map Ident Bool


--i swear this is what 15.4 says:
isArrayIndex e = 
  ELet nopos [("$isai", e)] $
    eAnd (isString (EId nopos "$isai"))
         (ELet nopos [("$intai", EOp nopos OToUInt32 [primToNum $ EId nopos "$isai"])] $
           (eAnd (eNot (strictEquality (EId nopos "$intai") (ENumber nopos 0xFFFFFFFF)))
                 (strictEquality (primToStr (EId nopos "$intai")) (EId nopos "$isai"))))


--helper since it's used in stmt too:
eAssignLVar :: Env -> String -> ExprPos -> ExprPos
eAssignLVar env x e = case M.lookup x env of
  Just True -> ESetRef nopos (EId nopos x) e
  Nothing -> ESetRef nopos (EId nopos "$global") 
                     (EUpdateField nopos (EDeref nopos $ EId nopos "$global")
                                   (EString nopos x)
                                   e)
  Just False -> error "eAssignLVar: assigning a non-assignable variable"

eVarRef :: Env -> String -> ExprPos
eVarRef env x = case M.lookup x env of
  Just True -> EDeref nopos (EId nopos x)
  Just False -> EId nopos x
  Nothing -> getGlobalVar x


--takes our expressions, writes out a new
--this takes in an arguments obj directly. used from String.split.
--TODO--sourcepos here?
eNewDirect :: ExprPos -> ExprPos -> ExprPos
eNewDirect eConstr argumentObj = 
  EApp nopos (EId nopos "@newDirect") [eConstr, argumentObj]

--this is the traditional list of exprs one:
eNew eConstr es = ELet1 nopos eConstr $ \c ->
  eNewDirect (EId nopos c) 
             (ERef nopos $ ERef nopos $ eArgumentsObj es (EId nopos c))

newError name msg = 
  EApp nopos (EId nopos "$makeException") 
    [EString nopos name, EString nopos (":" ++ msg)]




--for loop using our expressions. test better evaluate to a boolean!
--sets up the break/continue as well.
-- ForStmt _ init incr test body -> eFor (forInit env init) (maybeExpr env incr)
--    (toBoolean $ maybeExpr env test) (stmt env body)  

eFor init incr test body = ESeq (label init) init loop
 where loop = ELabel nopos "$break" $
                EWhile (label test) test (ESeq (label body) body' incr)
       body' = ELabel nopos "$continue" body



-- |Evaluate and lvalue, bind it to an identifier, pass the identifier to
-- 'bodyFn'.  'bodyFn' also receives a setter for the lvalue.
-- The setter manages various JavaScript details, including:
-- 11.2.1 (eval LHS), 11.13.1 (assignop), 8.7.2 (putValue), and 
-- 8.6.2.2 (Object put) and 15.4.5.1 (Array put).
theSetter :: Ident -> Ident -> (ExprPos -> ExprPos)
theSetter objRef fieldRef = \v -> ELet1 nopos v $ \vId -> 
  ESeq nopos (EIf nopos (strictEquality (EGetField nopos (EDeref nopos (EId nopos objRef)) (EString nopos "$class"))
                    (EString nopos "Array"))
         (EApp nopos (EId nopos "@setArray")
               (map (EId nopos) [objRef, fieldRef, vId]))
         (setObj objRef fieldRef (EId nopos vId)))
       (EId nopos vId)
  where setObj objRef field v = 
          ESetRef nopos (EId nopos objRef) 
                  (EUpdateField nopos (EDeref nopos (EId nopos objRef)) (EId nopos field) v)

withLValue :: Env 
           -> LValue SourcePos  
           -> (ExprPos -> (ExprPos -> ExprPos) -> ExprPos) -- ^getter, setter
           -> ExprPos
withLValue env (LVar a x) bodyFn = case M.lookup x env of
  Just True -> 
    bodyFn (EDeref nopos (EId a x)) 
            (\v -> ESeq nopos (ESetRef nopos (EId nopos x) v) (EDeref nopos (EId nopos x)))
  Nothing ->
    bodyFn (getGlobalVar x) $ \v ->
               EGetField nopos
                 (EDeref nopos
                   (ESetRef nopos (EId nopos "$global")
                            (EUpdateField nopos (EDeref nopos (EId nopos "$global"))
                                          (EString nopos x) v)))
                 (EString nopos x)
  Just False -> error "withLValue applied to a non-assignable value"
withLValue env (LDot a e x) bodyFn =
  ELet2 nopos (expr env e) (EString nopos x) $ \objRef field ->
    bodyFn (EGetField a (EDeref nopos (EId nopos objRef)) (EString nopos x))
           (theSetter objRef field)
withLValue env (LBracket a e1 e2) bodyFn =
  ELet2 nopos (expr env e1) (toString (expr env e2)) $ \objRef field ->
    bodyFn (EGetField a (EDeref nopos (EId nopos objRef)) (EId nopos field))
           (theSetter objRef field)



expr :: Env -> Expression SourcePos -> ExprPos
expr env e = case e of
  StringLit a s -> EString a s
  RegexpLit a s glob ci -> 
    eNew (EDeref a $ EId nopos "RegExp") [ --EId since we want the original one
      EString nopos s, EString nopos ((if glob then "g" else "") ++
                                (if ci   then "i" else ""))]
  --ArrayLit more or less follows 11.1.4 but does some things
  --more directly.
  ArrayLit a es -> 
    ERef a (EObject nopos ([ ("$class", EString nopos "Array")
                           , ("$proto", EId nopos "$Array.prototype")
                           , ("length", ENumber nopos (fromIntegral $ length es)) ]
                           ++ 
                           (map (\ix -> (show ix, expr env (es!!ix))) 
                                    [0..((length es)-1)])
                          ))
  NumLit a n -> ENumber a n
  IntLit a n -> ENumber a (fromIntegral n)
  BoolLit a b -> EBool a b
  NullLit a -> ENull a
  ObjectLit a ps -> ERef a $ EObject nopos $ 
    proto:("$class", EString nopos"Object"):
      (map (\(p,e') -> (prop p, expr env e')) ps)
      where proto = ("$proto", EId nopos "@Object_prototype")
  ThisRef a -> EId a "this" 
  VarRef _ (Id _ s) -> eVarRef env s
  -- PrefixDelete assumes that DotRef and BracketRef are desugared to iimmediate
  -- EGetField expressions.
  DotRef a1 e (Id a2 s) -> EGetField a1 (EDeref nopos $ toObject $ expr env e) 
                           (EString a2 s)
  BracketRef a e1 e2 -> 
    EGetField a (EDeref nopos $ toObject $ expr env e1) (toString $ expr env e2)
  NewExpr _ eConstr es -> eNew (expr env eConstr) (map (expr env) es)
  PrefixExpr _ op e -> prefixOp op (expr env e)
  UnaryAssignExpr a op lv -> withLValue env lv $ \get setter -> case op of
    PostfixInc -> ELet1 nopos get $ \x -> 
      ESeq nopos (setter $ EOp a ONumPlus [ENumber nopos 1, toNumber (EId nopos x)])
           (EId nopos x)
    PostfixDec -> ELet1 nopos get $ \x -> 
      ESeq nopos (setter $ EOp a ONumPlus [toNumber (EId nopos x), ENumber nopos (-1)])
           (EId nopos x)
    PrefixInc -> 
      ELet1 nopos (EOp a ONumPlus [toNumber get, ENumber nopos 1]) $ \v -> setter (EId nopos v)
    PrefixDec -> 
      ELet1 nopos (EOp a ONumPlus [toNumber get, ENumber nopos (-1)]) $ \v -> setter (EId nopos v)
  -- typeof e === string-constant is a common pattern that we desugar to
  -- something simpler, when we aren't checking for "object" or "function".
  InfixExpr a1 OpStrictEq (PrefixExpr a2 PrefixTypeof e) (StringLit a3 s)
    | s /= "function" && s /= "object" ->
    EOp a1 OStrictEq [EOp a2 OTypeof [expr env e], EString a3 s]
  InfixExpr _ op e1 e2 -> infixOp op (expr env e1) (expr env e2)
  CondExpr a e1 e2 e3 -> EIf a (toBoolean $ expr env e1) 
                             (expr env e2) (expr env e3)
  AssignExpr _ OpAssign lv e -> withLValue env lv $ \get setter ->
    setter (expr env e)
  --assuming that 'get' has no side effects, which withLValue should 
  --guarantee
  AssignExpr a op lv e -> withLValue env lv $ \get setter ->
    setter (infixOp iOp get (expr env e))
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
  ListExpr _ [] -> error "Desugar.hs: expr got empty ListExpr"
  ListExpr _ [e'] -> expr env e'
  ListExpr a (e':es) -> ESeq a (expr env e') (expr env (ListExpr a es))
  CallExpr a1 (DotRef a2 obj (Id a3 method)) args ->
    ELet nopos [("$obj", toObject $ expr env obj)] $
      applyObj (EGetField a1 (EDeref a2 $ EId nopos "$obj") (EString a3 method)) (EId nopos "$obj")
               (map (expr env) args)          
  CallExpr a e es -> 
    ELet nopos [("$obj", expr env e)] $
      EIf a (eNot (isRefComb isFunctionObj (EId nopos "$obj")))
          (EThrow nopos $ newError "TypeError" "CallExpr given non-function")
          (applyObj (EId nopos "$obj") (EId nopos "$global") (map (expr env) es))
  --TODO: don't just ignore mname                            
  FuncExpr a mname ids unliftedStmts -> 
    ERef a $ EObject nopos [("$code", code), 
                            ("arguments", arguments),
                            ("prototype", prototype),
                            ("$strRep", EString nopos strRep),
                            ("$proto", EId nopos "@Function_prototype")]
      where s = BlockStmt a (liftFuncStmts unliftedStmts)
            arg x ix = case x `S.member` assignableArgs of
              True -> ERef a $ EGetField nopos (EDeref nopos $ EDeref nopos (EId nopos "arguments"))
                                       (EString nopos $ show ix)
              False -> EGetField a (EDeref nopos $ EDeref nopos (EId nopos "arguments"))
                                 (EString nopos $ show ix)
            --cascade the lets in formals so that the rightmost one
            --is the one remaining
            --
            formals' = map (\(x, ix) -> (unId x, arg (unId x) ix)) 
                           (zip ids [0..])
            formals rest = foldr f rest formals'
            f bind rest = ELet nopos [bind] rest
            code = ELambda nopos ["this", "arguments"] $ 
                     formals $ 
                     ELet nopos locals $
                       ELabel nopos "$return" (stmt env' s)
            prototype = ERef nopos $ EObject nopos [("$proto", EId nopos "@Object_prototype"),
                                        ("$class", EString nopos "Object")]
            arguments = ENull nopos
            vars = localVars s
            locals = map (\x -> (x, (ERef nopos) (EUndefined nopos))) vars
            argSet = S.fromList (map unId ids)
            assignable = S.unions (map assignableVars unliftedStmts)
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


maybeExpr :: Env -> Maybe (Expression SourcePos) -> ExprPos
maybeExpr _ Nothing = EUndefined nopos
maybeExpr env (Just e) = expr env e

--{var x = 20; var x;} should have x be 20.
varDecl :: Env -> VarDecl SourcePos -> ExprPos
varDecl env (VarDecl a1 (Id a2 x) rhs) = case M.lookup x env of
    --True: it's a local var. if no declaration, don't do anything.
    Just True -> if (isNothing rhs) then EUndefined a1 else ESetRef a1 (EId a2 x) e
    -- It's global. if it exists, do nothing, else set to undefined.
    Nothing -> 
      if (isNothing rhs)
        then EIf nopos (EOp nopos OHasOwnProp [EDeref nopos $ EId nopos "$global", EString a2 x])
                 (EUndefined nopos) setglob
        else setglob
    Just False -> error "varDecl of a non-assignable variable"
                 
  where e = case rhs of
              Nothing -> EUndefined nopos
              Just e' -> expr env e'                                   
        setglob = ESetRef nopos (EId nopos "$global") 
                   (EUpdateField a1 (EDeref nopos $ EId nopos "$global")
                                 (EString a2 x) e)


forInit :: Env -> ForInit SourcePos -> ExprPos
forInit _ NoInit = EUndefined nopos
forInit env (VarInit decls) = foldr (ESeq nopos) (EUndefined nopos) (map (varDecl env) decls)
forInit env (ExprInit e) = expr env e


catchClause :: Env -> Maybe (CatchClause SourcePos) -> ExprPos
catchClause env Nothing = ELambda nopos ["x"] (EUndefined nopos)
catchClause env (Just (CatchClause a1 (Id a2 x) s)) = ELambda nopos [x] $
  ELet a1 [(x, ERef nopos (EId a2 x))] (stmt env' s)
  where env' = M.insert x True env


--The source position goes on the ESeq for both default and normal cases
caseClauses :: Ident -> Ident -> Env -> CaseClause SourcePos -> ExprPos -> ExprPos
caseClauses testId caseId env (CaseClause a e ss) remainingCases = 
  ELet nopos [(testId, EIf nopos (EId nopos testId)
                      (EBool nopos True) 
                      (EOp nopos OStrictEq [EId nopos caseId, expr env e]))] $
    ESeq a
      (EIf nopos (EId nopos testId)
           (foldr (\s e -> ESeq nopos (stmt env s) e) (EUndefined nopos) ss)
           (EUndefined nopos))
      remainingCases
caseClauses _ _ env (CaseDefault a ss) innerExpr =
   foldr (\s e -> ESeq a (stmt env s) e) innerExpr ss


stmt :: Env -> Statement SourcePos -> ExprPos
stmt env s = case s of
  BlockStmt a [] -> EUndefined a
  BlockStmt _ [s] -> stmt env s
  BlockStmt a (s:ss) -> ESeq a (stmt env s) (stmt env (BlockStmt a ss))
  EmptyStmt a -> EUndefined a
  ExprStmt _ e -> expr env e
  IfStmt a e s1 s2 -> case boolExpr e of
    True -> EIf a (expr env e) (stmt env s1) (stmt env s2)
    False -> EIf a (toBoolean $ expr env e) (stmt env s1) (stmt env s2)
  IfSingleStmt a e s1 -> EIf a (toBoolean $ expr env e) 
                         (stmt env s1)
                         (EUndefined nopos)
  WhileStmt a e1 s1 -> 
    ELabel nopos "$break" $
      EWhile a (toBoolean $ expr env e1) $
        ELabel nopos "$continue" 
          (stmt env s1)
  ForStmt _ init test incr body -> 
    eFor (forInit env init) (maybeExpr env incr)
         (toBoolean $ maybeExpr env test) (stmt env body)
  ThrowStmt a e -> EThrow a (expr env e)
  TryStmt a body catch finally -> -- TODO:  Not sure what gets nopos here
      EFinally a withoutFinally (maybeStmt env finally)
          where withoutFinally = 
                  ECatch nopos (stmt env body) (catchClause env catch)
  BreakStmt a Nothing -> EBreak a "$break" (EUndefined nopos)
  BreakStmt a (Just (Id _ lbl)) -> EBreak a lbl (EUndefined nopos)
  ContinueStmt a Nothing -> EBreak a "$continue" (EUndefined nopos)
  ContinueStmt a (Just (Id _ lbl)) -> EBreak a lbl (EUndefined nopos)
  LabelledStmt a (Id _ lbl) s1 -> ELabel a lbl (stmt env s1)
  ReturnStmt a Nothing -> EBreak a "$return" (EUndefined nopos)
  ReturnStmt a (Just e) -> EBreak a "$return" (expr env e)
  VarDeclStmt a decls -> foldr (ESeq nopos) (EUndefined nopos) (map (varDecl env) decls)
  FunctionStmt p _ _ _ -> 
    error $ "Desugar.hs : expected FunctionStmt at " ++ show p
  WithStmt _ obj body -> desugarWith (toObject $ expr env obj) (stmt env body)
  ForInStmt a (ForInVar (Id p x)) e s -> forin a p x e s
  -- TODO(arjun): arbitrary L-val allowed?
  ForInStmt a (ForInLVal (LVar p x)) e s -> forin a p x e s

  DoWhileStmt a s e ->
    let s' = stmt env s
        e' = expr env e
      in ELet nopos [("$doTest", ERef nopos $ EBool nopos True)]
              (EWhile a (eOr (EDeref nopos $ EId nopos "$doTest") e')
                        (ESeq nopos s' (ESetRef nopos (EId nopos "$doTest")
                                                      (EBool nopos False))))
  SwitchStmt a e cases ->
    ELet1 a (expr env e) $ \caseId ->
      ELabel nopos "$break" $
        ELet1 nopos (EBool nopos False) $ \testId ->
        foldr (caseClauses testId caseId env) (EUndefined nopos) cases
 where
  nyi s = error $ "Desugar.hs: " ++ s
  --TODO eventually: fix to work with any lhs
  forin a p x eObj body = --TODO: where does a go?
    ELet a [("$_finObj", expr env eObj),
            ("$finIter", ERef nopos $ EUndefined nopos)] $ --internal iterator
      --ECMA-breaking change: iterating thru undefined doesn't throw typeerr
      EIf nopos (eOr (isUndefined (EId nopos "$_finObj"))
                 (strictEquality (EId nopos "$_finObj") (ENull nopos)))
          (EUndefined nopos) $
          restfin a p x body
  restfin a p x body =    
    ELet nopos [("$finObj", toObject $ EId nopos "$_finObj")] $
      ELabel nopos "$break" $
        --while there is a next:
        EWhile nopos (EOp nopos OObjIterHasNext [EDeref nopos $ EId nopos "$finObj", 
                                     EDeref nopos $ EId nopos "$finIter"]) $
          (ELabel nopos "$continue" $
             --update our iterator
             ESeq nopos (ESetRef nopos (EId nopos "$finIter")
                           (EOp nopos OObjIterNext [EDeref nopos $ EId nopos "$finObj",
                                              EDeref nopos $ EId nopos "$finIter"]))$
               --get the value into the lvar and eval the body
               ELet nopos [("$curval", (EOp nopos OObjIterKey [EDeref nopos $ EId nopos "$finObj", 
                                        EDeref nopos $ EId nopos "$finIter"]))] $
                 --faking DontEnum: dont enum $ properties.
                 EIf nopos (EOp nopos OStrStartsWith [EId nopos "$curval", EString nopos "$"])
                     (EUndefined nopos)
                     (ESeq nopos (eAssignLVar env x (EId nopos "$curval"))
                               (stmt env body)))
          --if someone continues, it'll go into the while, and the
          --right thing should happen.


maybeStmt :: Env -> Maybe (Statement SourcePos) -> ExprPos
maybeStmt _ Nothing = EUndefined nopos
maybeStmt env (Just s) = stmt env s


desugarExpr :: Expression SourcePos -> (ExprPos -> ExprPos) -> ExprPos
desugarExpr e env = env (expr M.empty e)


desugarStmt :: Statement SourcePos -> (ExprPos -> ExprPos) -> ExprPos
desugarStmt s env = env (stmt M.empty s)

-- |Desugar a sequence of statements, in the given environment.  Instead of
-- producing EUndefined, the result of the sequence of statements is the
-- 'result' parameter.
desugarStmtsWithResult :: [Statement SourcePos] 
                       -> (ExprPos -> ExprPos) -> ExprPos -> ExprPos
desugarStmtsWithResult stmts env result = 
  env $ foldr (ESeq nopos) result (map (stmt M.empty) stmts')
          where stmts' = liftFuncStmts stmts


desugar :: JavaScript SourcePos -> (ExprPos -> ExprPos) -> ExprPos
desugar (Script _ ss) env = 
  desugarStmtsWithResult ss env (EUndefined nopos)
