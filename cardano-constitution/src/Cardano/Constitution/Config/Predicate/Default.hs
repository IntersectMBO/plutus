{-# LANGUAGE TemplateHaskell #-}
module Cardano.Constitution.Config.Predicate.Default
    ( defaultPredMeanings
    ) where

import Cardano.Constitution.Config.Predicate.DefaultUnresolved
import Cardano.Constitution.Config.Predicate.TH
import PlutusTx.AssocMap as Tx

{-# INLINABLE defaultPredMeanings #-}
defaultPredMeanings :: Tx.Map PredName PredMeaning
defaultPredMeanings = $$(resolvePredMeanings defaultPredMeaningsUnresolved)
