{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE StrictData           #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutus.PAB.Webserver.Types where

import           Cardano.BM.Data.Tracer                  (ToObject, toObject)
import           Cardano.BM.Data.Tracer.Extras           (StructuredLog, mkObjectStr)
import qualified Cardano.Metadata.Types                  as Metadata
import           Data.Aeson                              (FromJSON, ToJSON)
import           Data.Map                                (Map)
import           Data.Tagged                             (Tagged (Tagged))
import           Data.Text                               (Text)
import           Data.Text.Prettyprint.Doc               (Pretty, pretty, viaShow, (<+>))
import           Data.UUID                               (UUID)
import           GHC.Generics                            (Generic)
import           Ledger                                  (Tx, TxId)
import           Ledger.Index                            (UtxoIndex)
import           Playground.Types                        (FunctionSchema)
import           Plutus.PAB.Effects.Contract.ContractExe (ContractExe)
import           Plutus.PAB.Events                       (PABEvent)
import           Plutus.PAB.Events.Contract              (ContractPABRequest)
import           Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse)
import           Schema                                  (FormSchema)
import           Wallet.Rollup.Types                     (AnnotatedTx)
import           Wallet.Types                            (ContractInstanceId)

data ContractReport t =
    ContractReport
        { crAvailableContracts   :: [ContractSignatureResponse t]
        , crActiveContractStates :: [(ContractInstanceId, PartiallyDecodedResponse ContractPABRequest)]
        }
    deriving stock (Generic, Eq, Show)
    deriving anyclass (ToJSON, FromJSON)

data ChainReport =
    ChainReport
        { transactionMap      :: Map TxId Tx
        , utxoIndex           :: UtxoIndex
        , annotatedBlockchain :: [[AnnotatedTx]]
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

emptyChainReport :: ChainReport
emptyChainReport = ChainReport mempty mempty mempty

data FullReport t =
    FullReport
        { contractReport :: ContractReport t
        , chainReport    :: ChainReport
        }
    deriving stock (Generic, Eq, Show)
    deriving anyclass (ToJSON, FromJSON)

data ContractSignatureResponse t =
    ContractSignatureResponse
        { csrDefinition :: t
        , csrSchemas    :: [FunctionSchema FormSchema]
        }
    deriving stock (Generic, Eq, Show)
    deriving anyclass (ToJSON, FromJSON)

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
    | NewPABEvents [PABEvent ContractExe]
    | FetchedProperties (Metadata.SubjectProperties 'Metadata.AesonEncoding)
    | FetchedProperty Metadata.Subject (Metadata.Property 'Metadata.AesonEncoding)
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
