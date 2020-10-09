{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}

module Plutus.SCB.Webserver.Types where

import           Cardano.BM.Data.Tracer        (ToObject, toObject)
import           Cardano.BM.Data.Tracer.Extras (StructuredLog, mkObjectStr)
import qualified Cardano.Metadata.Types        as Metadata
import           Data.Aeson                    (FromJSON, ToJSON)
import           Data.Map                      (Map)
import           Data.Text                     (Text)
import           Data.Text.Prettyprint.Doc     (Pretty, pretty, viaShow, (<+>))
import           Data.UUID                     (UUID)
import           GHC.Generics                  (Generic)
import           IOTS                          (Tagged (Tagged))
import           Ledger                        (Tx, TxId)
import           Ledger.Index                  (UtxoIndex)
import           Playground.Types              (FunctionSchema)
import           Plutus.SCB.Events             (ChainEvent, ContractInstanceState)
import           Plutus.SCB.Types              (ContractExe)
import           Schema                        (FormSchema)
import           Wallet.Rollup.Types           (AnnotatedTx)

data ContractReport t =
    ContractReport
        { crAvailableContracts   :: [ContractSignatureResponse t]
        , crActiveContractStates :: [ContractInstanceState t]
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

data ChainReport =
    ChainReport
        { transactionMap      :: Map TxId Tx
        , utxoIndex           :: UtxoIndex
        , annotatedBlockchain :: [[AnnotatedTx]]
        , relatedMetadata     :: Map Metadata.Subject [Metadata.Property 'Metadata.AesonEncoding]
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

data FullReport t =
    FullReport
        { contractReport :: ContractReport t
        , chainReport    :: ChainReport
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

data StreamToServer
    = FetchProperties Metadata.Subject
    | FetchProperty Metadata.Subject Metadata.PropertyKey
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

deriving via (Tagged "stream_to_server" StreamToServer) instance
         StructuredLog StreamToServer

data StreamToClient
    = NewChainReport ChainReport
    | NewContractReport (ContractReport ContractExe)
    | NewChainEvents [ChainEvent ContractExe]
    | FetchedProperties (Maybe (Metadata.SubjectProperties 'Metadata.AesonEncoding))
    | FetchedProperty Metadata.Subject (Maybe (Metadata.Property 'Metadata.AesonEncoding))
    | ErrorResponse Text
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

deriving via (Tagged "stream_to_client" StreamToClient) instance
         StructuredLog StreamToClient

data WebSocketLogMsg
    = CreatedConnection UUID
    | ClosedConnection UUID
    | ReceivedWebSocketRequest (Either Text StreamToServer)
    | SendingWebSocketResponse StreamToClient
    deriving  (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty WebSocketLogMsg where
    pretty (CreatedConnection uuid) =
        "Created WebSocket conection:" <+> viaShow uuid
    pretty (ClosedConnection uuid) =
        "Closed WebSocket conection:" <+> viaShow uuid
    pretty (ReceivedWebSocketRequest request) =
        "Received WebSocket request:" <+> viaShow request
    pretty (SendingWebSocketResponse response) =
        "Sending WebSocket response:" <+> viaShow response

instance ToObject WebSocketLogMsg where
    toObject _ =
        \case
            CreatedConnection u -> mkObjectStr "created connection" u
            ClosedConnection u -> mkObjectStr "closed connection" u
            ReceivedWebSocketRequest request ->
                mkObjectStr "received websocket request" request
            SendingWebSocketResponse response ->
                mkObjectStr "sending websocket response" response
