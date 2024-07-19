{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RankNTypes      #-}
module Cardano.Constitution.Config
    ( defaultPredMeanings
    , module Export
    ) where

import Cardano.Constitution.Config.Instance.FromJSON ()
import Cardano.Constitution.Config.Instance.TxLift ()
import Cardano.Constitution.Config.Types as Export
import PlutusTx.Eq as Tx
import PlutusTx.Ord as Tx

{-# INLINABLE defaultPredMeanings #-}
-- | NOTE: **BE CAREFUL** of the ordering. Expected value is first arg, Proposed Value is second arg
defaultPredMeanings :: PredKey -> PredMeaning a
defaultPredMeanings = \case
    MinValue -> (Tx.<=)
    MaxValue -> (Tx.>=)
    NotEqual -> (Tx./=)
