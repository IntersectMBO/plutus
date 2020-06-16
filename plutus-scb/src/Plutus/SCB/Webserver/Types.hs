{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}

module Plutus.SCB.Webserver.Types where

import           Data.Aeson             (FromJSON, ToJSON)
import           Data.Map               (Map)
import           GHC.Generics           (Generic)
import           Ledger                 (PubKeyHash, Tx, TxId)
import           Ledger.Index           (UtxoIndex)
import           Playground.Types       (FunctionSchema)
import           Plutus.SCB.Events      (ChainEvent, ContractInstanceState)
import           Schema                 (FormSchema)
import           Wallet.Emulator.Wallet (Wallet)
import           Wallet.Rollup.Types    (AnnotatedTx)

data FullReport t =
    FullReport
        { latestContractStatuses :: [ContractInstanceState t]
        , events                 :: [ChainEvent t]
        , transactionMap         :: Map TxId Tx
        , utxoIndex              :: UtxoIndex
        , annotatedBlockchain    :: [[AnnotatedTx]]
        , walletMap              :: Map PubKeyHash Wallet
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

newtype ContractSignatureResponse t = ContractSignatureResponse [FunctionSchema FormSchema]
    deriving (Show, Eq, Generic)
    deriving newtype (FromJSON, ToJSON)
