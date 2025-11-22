{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusTx.Blueprint.PlutusVersion where

import Prelude

import Data.Aeson (ToJSON (..))

{-| A "Plutus Version", as defined by the CIP-0057
|
| This version corresponds to the "Plutus Ledger Language Version"
| defined by the plutus-tx-plugin. -}
data PlutusVersion = PlutusV1 | PlutusV2 | PlutusV3
  deriving stock (Show)

instance ToJSON PlutusVersion where
  toJSON = \case
    PlutusV1 -> "v1"
    PlutusV2 -> "v2"
    PlutusV3 -> "v3"
