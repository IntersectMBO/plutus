{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StrictData         #-}

module Plutus.SCB.Webserver.Types where

import           Data.Aeson                (FromJSON, ToJSON)
import           Data.Map                  (Map)
import           Data.Text                 (Text)
import           Data.Text.Prettyprint.Doc (Pretty, pretty, viaShow, (<+>))
import           Data.UUID                 (UUID)
import           GHC.Generics              (Generic)
import           Ledger                    (PubKeyHash, Tx, TxId)
import           Ledger.Index              (UtxoIndex)
import           Playground.Types          (FunctionSchema)
import           Plutus.SCB.Events         (ChainEvent, ContractInstanceState)
import           Schema                    (FormSchema)
import           Wallet.Emulator.Wallet    (Wallet)
import           Wallet.Rollup.Types       (AnnotatedTx)

data ContractReport t =
    ContractReport
        { crAvailableContracts   :: [ContractSignatureResponse t]
        , crActiveContractStates :: [ContractInstanceState t]
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

data ContractSignatureResponse t =
    ContractSignatureResponse
        { csrDefinition :: t
        , csrSchemas    :: [FunctionSchema FormSchema]
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

newtype StreamToServer t =
    Ping Text
    deriving (Show, Eq, Generic)
    deriving newtype (FromJSON, ToJSON)

data StreamToClient t
    = NewChainReport (ChainReport t)
    | NewContractReport (ContractReport t)
    | NewChainEvents [ChainEvent t]
    | Echo Text
    | ErrorResponse Text
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

data WebSocketLogMsg
    = CreatedConnection UUID
    | ClosedConnection UUID

instance Pretty WebSocketLogMsg where
    pretty (CreatedConnection uuid) =
        "Created WebSocket conection:" <+> viaShow uuid
    pretty (ClosedConnection uuid) =
        "Closed WebSocket conection:" <+> viaShow uuid
