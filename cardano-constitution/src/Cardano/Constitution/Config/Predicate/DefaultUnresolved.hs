{-# LANGUAGE TemplateHaskell #-}
module Cardano.Constitution.Config.Predicate.DefaultUnresolved
    ( defaultPredMeaningsUnresolved
    ) where

import Cardano.Constitution.Config.Predicate.Types
import PlutusTx.AssocMap as Tx
import PlutusTx.Builtins qualified as Tx

import Language.Haskell.TH qualified as TH

{-# INLINABLE defaultPredMeaningsUnresolved #-}
-- NOTE: **BE CAREFUL** of the ordering. Expected value is first arg, Proposed Value is second arg
defaultPredMeaningsUnresolved :: Tx.Map PredName TH.Name
defaultPredMeaningsUnresolved = Tx.fromList
             [ (MinValue, 'Tx.lessThanEqualsInteger)
             , (MaxValue, 'Tx.greaterThanEqualsInteger)
             ]
