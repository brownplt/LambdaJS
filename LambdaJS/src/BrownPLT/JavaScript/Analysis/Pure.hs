module BrownPLT.JavaScript.Analysis.Pure 
  ( isPure
  , isPureExp
  , isPureBindExp
  , isPureAssocs
  ) where

import Data.Generics

import BrownPLT.JavaScript.Semantics.Syntax ( Ident )
import BrownPLT.JavaScript.Semantics.ANF ( Value(..), BindExp(..), Exp(..) )

-- Is a value pure?
--
-- For 'Exp' and 'BindExp', use the appropriate definition. A 'Value' does not
-- produce side-effects. That goes for 'VLambda', even if its body does contain
-- side-effects.
--
isPure :: forall a c. (Data a, Typeable1 c) => c a -> Bool
isPure = True `mkQ`  (isPureExp      :: Exp     a -> Bool)
              `extQ` (isPureBindExp  :: BindExp a -> Bool)

isPureExp :: forall a. Data a => Exp a -> Bool
isPureExp = gmapQl (&&) True
                 (True `mkQ`  (isPureExp    :: Exp     a -> Bool)
                     `extQ` (isPureBindExp  :: BindExp a -> Bool)
                     `extQ` (isPureAssocs   :: [(Ident, BindExp a)] -> Bool))

-- A 'BindExp' isn't pure if it's a 'BSetRef' or a 'BApp'. However, if
-- the function position of a 'BApp' is a literal 'VLambda', we can say that
-- the expression is pure if the body of the 'VLambda' is pure. This probably
-- doesn't happen much in practice.
--
isPureBindExp :: forall a. Data a => BindExp a -> Bool
isPureBindExp (BSetRef _ _ _) = False
isPureBindExp (BApp _ v _)    = case v of
    VLambda _ _ b -> isPureExp b
    otherwise     -> False
isPureBindExp e = gmapQl (&&) True
                    (True `mkQ` (isPureExp   :: Exp a -> Bool)
                       `extQ` (isPureBindExp :: BindExp a -> Bool)) e

isPureAssocs :: forall a c b. (Data a, Typeable1 c) => [(b, c a)] -> Bool
isPureAssocs = all (isPure . snd)
