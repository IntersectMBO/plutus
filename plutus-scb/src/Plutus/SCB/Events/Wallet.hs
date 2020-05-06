{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Plutus.SCB.Events.Wallet where

import           Data.Aeson   (FromJSON, ToJSON)
import           GHC.Generics (Generic)
import           Ledger       (Tx)

newtype WalletEvent =
    BalancedTx Tx
    deriving (Show, Eq, Generic)
    deriving newtype (FromJSON, ToJSON)
