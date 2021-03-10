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
import           Plutus.PAB.Effects.Contract             (PABContract (..))
import           Plutus.PAB.Effects.Contract.CLI         (ContractExe)
import           Plutus.PAB.Events.ContractInstanceState (ContractInstanceState)
import           Schema                                  (FormSchema)
import           Wallet.Rollup.Types                     (AnnotatedTx)
import           Wallet.Types                            (ContractInstanceId)

data ContractReport t =
    ContractReport
        { crAvailableContracts   :: [ContractSignatureResponse t]
        , crActiveContractStates :: [(ContractInstanceId, [Request ContractPABRequest])]
        }
    deriving stock (Generic)

deriving stock instance (Show (ContractDef t)) => Show (ContractReport t)
deriving stock instance (Eq (ContractDef t)) => Eq (ContractReport t)
deriving anyclass instance (ToJSON (ContractDef t)) => ToJSON (ContractReport t)
deriving anyclass instance (FromJSON (ContractDef t)) => FromJSON (ContractReport t)

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
    deriving stock Generic

deriving stock instance (Show (ContractDef t)) => Show (FullReport t)
deriving stock instance (Eq (ContractDef t)) => Eq (FullReport t)
deriving anyclass instance (ToJSON (ContractDef t)) => ToJSON (FullReport t)
deriving anyclass instance (FromJSON (ContractDef t)) => FromJSON (FullReport t)

data ContractSignatureResponse t =
    ContractSignatureResponse
        { csrDefinition :: ContractDef t
        , csrSchemas    :: [FunctionSchema FormSchema]
        }
    deriving stock (Generic)

deriving stock instance (Show (ContractDef t)) => Show (ContractSignatureResponse t)
deriving stock instance (Eq (ContractDef t)) => Eq (ContractSignatureResponse t)
deriving anyclass instance (ToJSON (ContractDef t)) => ToJSON (ContractSignatureResponse t)
deriving anyclass instance (FromJSON (ContractDef t)) => FromJSON (ContractSignatureResponse t)

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
