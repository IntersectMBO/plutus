{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}

module Plutus.SCB.Webserver.Types where

import           Data.Aeson             (FromJSON, ToJSON)
import           Data.Map               (Map)
import           Data.Set               (Set)
import           GHC.Generics           (Generic)
import           Ledger                 (PubKeyHash, Tx, TxId)
import           Ledger.Index           (UtxoIndex)
import           Playground.Types       (FunctionSchema)
import           Plutus.SCB.Events      (ChainEvent, ContractInstanceState)
import           Schema                 (FormSchema)
import           Wallet.Emulator.Wallet (Wallet)
import           Wallet.Rollup.Types    (AnnotatedTx)

data ContractReport t =
    ContractReport
        { installedContracts :: Set t
        , contractStates     :: [ContractInstanceState t]
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

data ChainReport t =
    ChainReport
        { transactionMap      :: Map TxId Tx
        , utxoIndex           :: UtxoIndex
        , annotatedBlockchain :: [[AnnotatedTx]]
        , walletMap           :: Map PubKeyHash Wallet
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

data FullReport t =
    FullReport
        { contractReport :: ContractReport t
        , chainReport    :: ChainReport t
        , events         :: [ChainEvent t]
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

newtype ContractSignatureResponse t =
    ContractSignatureResponse [FunctionSchema FormSchema]
    deriving (Show, Eq, Generic)
    deriving newtype (FromJSON, ToJSON)
