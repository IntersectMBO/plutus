{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}

module Plutus.SCB.Webserver.Types where

import           Data.Aeson             (FromJSON, ToJSON)
import           Data.Map               (Map)
import           Data.UUID              (UUID)
import           GHC.Generics           (Generic)
import           Ledger                 (PubKeyHash, Tx, TxId)
import           Ledger.Index           (UtxoIndex)
import           Plutus.SCB.Events      (ChainEvent)
import           Plutus.SCB.Types       (ActiveContractState)
import           Wallet.Emulator.Wallet (Wallet)
import           Wallet.Rollup.Types    (AnnotatedTx)

data FullReport t =
    FullReport
        { latestContractStatus :: Map UUID (ActiveContractState t)
        , events               :: [ChainEvent t]
        , transactionMap       :: Map TxId Tx
        , utxoIndex            :: UtxoIndex
        , annotatedBlockchain  :: [[AnnotatedTx]]
        , walletMap            :: Map PubKeyHash Wallet
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)
