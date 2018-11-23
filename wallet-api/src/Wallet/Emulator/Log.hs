{-# LANGUAGE DeriveGeneric #-}
module Wallet.Emulator.Log(
    EmulatorEvent(..)
    ) where

import           Data.Aeson        (FromJSON, ToJSON)
import           GHC.Generics      (Generic)

import qualified Wallet.UTXO.Index as UTXO
import qualified Wallet.UTXO.Types as UTXO

-- | Events produced by the mockchain
data EmulatorEvent =
    TxnSubmit UTXO.TxId'
    -- ^ A transaction has been added to the global pool of pending transactions
    | TxnValidate UTXO.TxId'
    -- ^ A transaction has been validated and added to the blockchain
    | TxnValidationFail UTXO.TxId' UTXO.ValidationError
    -- ^ A transaction failed  to validate
    | BlockAdd UTXO.Height
    -- ^ A block has been added to the blockchain
    deriving (Eq, Ord, Show, Generic)

instance FromJSON EmulatorEvent
instance ToJSON EmulatorEvent
