module BrownPLT.JavaScript.Analysis.FreeVars
  ( freeVars
  , freeVarsValue
  , freeVarsExp
  , freeVarsBindExp
  ) where

import Data.Set ( Set )
import qualified Data.Set as S
import Data.Generics

import BrownPLT.JavaScript.Semantics.Syntax ( Ident )
import BrownPLT.JavaScript.Semantics.ANF ( Value(..), BindExp(..), Exp(..) )

freeVars :: forall a c. (Data a, Typeable1 c) => c a -> Set Ident
freeVars = S.empty
                `mkQ`  (freeVarsBindExp  :: BindExp a  -> Set Ident)
                `extQ` (freeVarsExp      :: Exp     a  -> Set Ident)
                `extQ` (freeVarsValue    :: Value   a  -> Set Ident)

freeVarsValue :: forall a. Data a => Value a -> Set Ident
freeVarsValue v = case v of
  VId     _ id     -> S.singleton id
  VLambda _ args e -> (freeVarsExp e) `S.difference` (S.fromList args)
  otherwise        -> S.empty

freeVarsValueLst :: forall a. Data a => [Value a] -> Set Ident
freeVarsValueLst = S.unions . map freeVarsValue

freeVarsExp :: forall a. Data a => Exp a -> Set Ident
freeVarsExp e = case e of
  ALet _ binds e -> 
    let (ids, bes) = unzip binds
        fvbes      = map freeVarsBindExp bes
      in (S.unions fvbes) 
            `S.union` ((freeVarsExp e) `S.difference` (S.fromList ids))
  otherwise -> 
    S.unions $ gmapQ (S.empty
                        `mkQ`  (freeVarsBindExp  :: BindExp a  -> Set Ident)
                        `extQ` (freeVarsExp      :: Exp     a  -> Set Ident)
                        `extQ` (freeVarsValue    :: Value   a  -> Set Ident)) e

freeVarsBindExp :: forall a. Data a => BindExp a -> Set Ident
freeVarsBindExp be =
    S.unions $ gmapQ (S.empty
                        `mkQ`  (freeVarsBindExp    :: BindExp a  -> Set Ident)
                        `extQ` (freeVarsExp        :: Exp     a  -> Set Ident)
                        `extQ` (freeVarsValue      :: Value   a  -> Set Ident)
                        `extQ` (freeVarsValueLst   :: [Value  a] -> Set Ident)
                        `extQ` (freeVarsValueAssoc 
                                    :: [(String, Value  a)] -> Set Ident)) be
  where 
    freeVarsValueLst   = S.unions . map freeVarsValue
    freeVarsValueAssoc = S.unions . map (freeVarsValue . snd)
