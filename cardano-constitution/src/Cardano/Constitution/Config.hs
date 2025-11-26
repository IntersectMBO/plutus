{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module Cardano.Constitution.Config
  ( defaultConstitutionConfig
  , defaultPredMeanings
  , module Export
  ) where

import Cardano.Constitution.Config.Instance.FromJSON ()
import Cardano.Constitution.Config.Instance.TxLift ()
import Cardano.Constitution.Config.Types as Export
import Cardano.Constitution.DataFilePaths as DFP
import PlutusTx.Eq as Tx
import PlutusTx.Ord as Tx

import Data.Aeson.THReader as Aeson

-- | The default config read from "data/defaultConstitution.json"
defaultConstitutionConfig :: ConstitutionConfig
defaultConstitutionConfig = $$(Aeson.readJSONFromFile DFP.defaultConstitutionConfigFile)
{-# INLINEABLE defaultConstitutionConfig #-}

-- | NOTE: **BE CAREFUL** of the ordering. Expected value is first arg, Proposed Value is second arg
defaultPredMeanings :: PredKey -> PredMeaning a
defaultPredMeanings = \case
  MinValue -> (Tx.<=)
  MaxValue -> (Tx.>=)
  NotEqual -> (Tx./=)
{-# INLINEABLE defaultPredMeanings #-}
