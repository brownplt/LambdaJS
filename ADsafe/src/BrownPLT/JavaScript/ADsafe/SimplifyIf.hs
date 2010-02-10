module BrownPLT.JavaScript.ADsafe.SimplifyIf ( ifReduce ) where

import BrownPLT.JavaScript.Semantics.ANF
import BrownPLT.JavaScript.Semantics.Syntax

import Data.Generics

import qualified Data.Map as M
import qualified Data.Set as S

data RType = RNumber
           | RObject
           | RFunction
           | RString
           | RBool
           | RLocation
           | RNull
           | RUndefined
           | REval
           | RAny
             deriving (Show, Ord, Eq)
             
data AType = AString String --constant strings
           | AVar [RType]   --possible variable types for an ident/expr
           | ATypeOf Ident  --expression holding the type of an ident
           | ATypeIs Ident RType
           | ATypeIsNot Ident RType
             deriving (Show, Ord, Eq)

data T = A AType
       | R RType

allT = [RNumber, RObject, RString, RFunction, 
        RBool, RLocation, RNull, RUndefined]

type TEnv = M.Map Ident T

stringType :: String -> RType
stringType s =
    case s of
      "string" -> RString
      "number" -> RNumber
      "undefined" -> RUndefined
      "null" -> RNull
      "object" -> RObject
      "boolean" -> RBool
      "function" -> RFunction
      "location" -> RLocation
      otherwise -> RAny
      -- don't check for eval here -- we don't check with typeof

single :: RType -> T
single r = A (AVar [r])

union :: T -> T -> T
union (A (AVar r1)) (A (AVar r2)) = 
    A (AVar (S.toList (S.union (S.fromList r1) (S.fromList r2))))
union (A (AVar r1)) (R r) = A (AVar (r:r1))
union (R r) (A (AVar r1)) = A (AVar (r:r1))
union a b = (A (AVar allT))

remove :: RType -> T -> T
remove r (A (AVar ts)) = 
    A (AVar (S.toList (S.delete r (S.fromList ts))))
remove r t = t

-- returns the new value and the type for it
typeVal :: Data a => TEnv -> Value a -> (Value a, T)
typeVal env v =
    case v of
      VString a s -> (v, A (AString s))
      VId a x -> (v, case M.lookup x env of 
                       Just t -> t
                       Nothing -> A (AVar allT))
      VLambda a ids body ->
          (VLambda a ids (fst (typeExp env body)), 
           single RFunction)
      VNumber a n -> (v, single RNumber)
      VBool a n -> (v, single RBool)
      VUndefined a -> (v, single RUndefined)
      VNull a -> (v, single RNull)
      VEval a -> (v, single REval)


typeBind :: Data a => TEnv -> BindExp a -> (BindExp a, T)
typeBind env b =
    case b of
      BObject a fields -> 
          let newfields = (zip (map fst fields)
                           (map fst 
                            (map (typeVal env) 
                             (map snd fields)))) in
          (BObject a newfields, R RObject)
      BSetRef a id v2 ->
          let (v2', t2) = typeVal env v2 
            in (BSetRef a id v2', t2)
      BRef a v ->
          let (v', t) = typeVal env v in
          (BRef a v', R RLocation)
      BDeref a v ->
          let (v', t) = typeVal env v in
          (BDeref a v', A (AVar allT))  -- we know nothing about refs
      BGetField a v1 v2 ->
          let (v1', t1) = typeVal env v1
              (v2', t2) = typeVal env v2 in
          (BGetField a v1' v2', A (AVar allT)) -- we know nothing about objects
      BUpdateField a v1 v2 v3 ->
          let (v1', t1) = typeVal env v1
              (v2', t2) = typeVal env v2
              (v3', t3) = typeVal env v3 in
          (BUpdateField a v1' v2' v3', R RObject)
      BDeleteField a v1 v2 ->
          let (v1', t1) = typeVal env v1
              (v2', t2) = typeVal env v2 in
          (BDeleteField a v1' v2', R RUndefined)
      BValue a v ->
          let (v', t) = typeVal env v in
          (BValue a v', t)
      BApp a f xs ->
          let xs' = map fst (map (typeVal env) xs)
              (f', t) = typeVal env f in
          (BApp a f' xs', A (AVar allT))
      BIf a c (AReturn a1 (VBool a2 False)) (AReturn a3 (VBool a4 True)) ->
          let (c', tc) = typeVal env c
              rettype = case tc of
                          A (ATypeIs x t) -> A (ATypeIsNot x t)
                          A (ATypeIsNot x t) -> A (ATypeIs x t)
                          otherwise -> single RBool in
          (BIf a c' (AReturn a1 (VBool a2 False)) (AReturn a3 (VBool a4 True)), rettype)
      BIf a c thn els ->
          let (c', tc) = typeVal env c in
          case tc of 
            A (ATypeIs x t) -> 
                let tx = snd (typeVal env (VId a x)) in
                case tx of
                  A (AVar [r]) | r == t ->
                      let (thn', t_thn) = typeExp env thn in
                      (BApp a (VLambda a [] thn') [], t_thn)
                  A (AVar ts) ->
                      if (S.member t (S.fromList ts)) then
                          let (thn', t_thn) = typeExp (M.insert x (single t) env) thn
                              (els', t_els) = typeExp (M.insert x (remove t tx) env) els in
                          (BIf a c' thn' els', union t_thn t_els)
                      else
                          let (els', t_els) = typeExp env els in
                          (BApp a (VLambda a [] els') [], t_els)
                  otherwise -> defaultIf env b
            A (ATypeIsNot x t) -> 
                let tx = snd (typeVal env (VId a x)) in
                case tx of
                  A (AVar [r]) | r == t ->
                      let (els', t_els) = typeExp env els in
                      (BApp a (VLambda a [] els') [], t_els)
                  A (AVar ts) ->
                      if (S.member t (S.fromList ts)) then
                          let (thn', t_thn) = typeExp (M.insert x (remove t tx) env) thn
                              (els', t_els) = typeExp (M.insert x (single t) env) els in
                          (BIf a c' thn' els', union t_thn t_els)
                      else
                          let (thn', t_thn) = typeExp env thn in
                          (BApp a (VLambda a [] thn') [], t_thn)
                  otherwise -> defaultIf env b
            otherwise -> defaultIf env b
      BOp a op xs -> bop env b

bop :: Data a => TEnv -> BindExp a -> (BindExp a, T)
bop env b =
    case b of
      BOp a OStrictEq [x, y] ->
          let (x', tx) = typeVal env x
              (y', ty) = typeVal env y in
          case (tx, ty) of
            (A (ATypeOf ident), A (AString s)) -> 
                (BOp a OStrictEq [x', y'], (A (ATypeIs ident (stringType s))))
            (A (AString s), A (ATypeOf ident)) -> 
                (BOp a OStrictEq [x', y'], (A (ATypeIs ident (stringType s))))
            otherwise -> 
                (BOp a OStrictEq [x', y'], single RBool)
      BOp a1 OTypeof [(VId a2 x)] ->
          let (x', tx) = typeVal env (VId a2 x) in
          (BOp a1 OTypeof [x'], A (ATypeOf x))
      BOp a1 OSurfaceTypeof [(VId a2 x)] ->
          let (x', tx) = typeVal env (VId a2 x) in
          (BOp a1 OSurfaceTypeof [x'], A (ATypeOf x))
      BOp a OPrimToBool [x] -> 
          let (x', tx) = typeVal env x in
          let rettype = case tx of
                          A (ATypeIs y r) -> A (ATypeIs y r)
                          A (ATypeIsNot y r) -> A (ATypeIsNot y r)
                          otherwise -> single RBool in
          (BOp a OPrimToBool [x'], rettype)
      BOp a op xs ->
          let xs' = map fst (map (typeVal env) xs)
              ts = map snd (map (typeVal env) xs) in
          (BOp a op xs', single (opType op))
      otherwise -> (b, single RUndefined)


opType :: Op -> RType
opType op = 
    if S.member op (S.fromList [ONumPlus, OMul, ODiv, OMod, OSub, OLt, OBAnd, OBOr, OBXOr, OBNot, OLShift, OSpRShift, OZfRShift, OPrimToNum, OMathExp, OMathLog, OMathCos, OMathSin, OMathAbs, OMathPow, OStrLen, OToInteger, OToInt32, OToUInt32])
    then
        RNumber
    else
        if S.member op (S.fromList [OStrPlus, OStrSplitRegExp, OStrSplitStrExp])
        then
            RString
        else
            RBool
      
defaultIf :: Data a => TEnv -> BindExp a -> (BindExp a, T)
defaultIf env b = 
    case b of
      BIf a c t e ->
          let (c', tc) = typeVal env c
              (t', tt) = typeExp env t
              (e', te) = typeExp env e in
          (BIf a c' t' e', union tt te)
      otherwise -> (b, single RUndefined) -- this should never happen

typeExp :: Data a => TEnv -> Exp a -> (Exp a, T)
typeExp env e = 
    case e of 
      ALet a binds body ->
          let pairs = map (typeBind env) (map snd binds)
              (xs, ts) = (map fst pairs, map snd pairs)
              binds' = zip (map fst binds) (xs)
              env' = foldl (\acc_env pair -> 
                                 M.insert (fst pair) (snd pair) acc_env)
                      env (zip (map fst binds) ts)
              (body', tbody) = typeExp env' body in
          (ALet a binds' body', tbody)
      ARec a binds body ->
          let pairs = map (typeVal env) (map snd binds)
              (xs, ts) = (map fst pairs, map snd pairs)
              binds' = zip (map fst binds) (xs)
              env' = foldl (\acc_env pair -> 
                                 M.insert (fst pair) (snd pair) acc_env)
                      env (zip (map fst binds) ts)
              (body', tbody) = typeExp env' body in
          (ARec a binds' body', tbody)
      ALabel a lbl body ->
          let (body', tbody) = typeExp env body in
          (ALabel a lbl body', tbody)
      ABreak a lbl v ->
          let (v', tv) = typeVal env v in
          (ABreak a lbl v', tv)
      AThrow a v ->
          let (v', tv) = typeVal env v in
          (AThrow a v', tv)
      ACatch a body catch ->
          let (body', tbody) = typeExp env body
              (catch', tcatch) = typeVal env catch in
          (ACatch a body' catch', union tbody tcatch)
      AFinally a body final ->
          let (body', tbody) = typeExp env body
              (final', tfinal) = typeExp env final in
          (AFinally a body' final', union tbody tfinal)
      AReturn a v ->
          let (v', tv) = typeVal env v in
          (AReturn a v', tv)
      ABind a b ->
          let (b', tb) = typeBind env b in
          (ABind a b', tb)
                                 
          
ifReduce :: Data a => Exp a -> Exp a                       
ifReduce e = fst (typeExp M.empty e)
