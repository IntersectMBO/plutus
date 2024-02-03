{-# LANGUAGE TemplateHaskell #-}
module Cardano.Constitution.Config.Predicate.TH
    ( resolvePredMeanings
    , module Export
    ) where

import Cardano.Constitution.Config.Predicate.Types as Export
import Cardano.Constitution.Config.Types as Export

import Language.Haskell.TH qualified as TH
import PlutusTx.AssocMap qualified as Tx

-- | Turns the Map's `values` (template-haskell's 'Name's) to their
-- actual runtime representation (functions of Integer -> Integer -> Bool)
resolvePredMeanings :: Tx.Map PredName TH.Name -> TH.Code TH.Q (Tx.Map PredName PredMeaning)
resolvePredMeanings predMeaningsNames = do
    let exps = (\ (key,name) -> [| (key, $(TH.varE name)) |])
               <$> Tx.toList predMeaningsNames
    [|| Tx.fromList $$(TH.unsafeCodeCoerce (TH.listE exps)) :: Tx.Map PredName PredMeaning ||]
