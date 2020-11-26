{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
-- | SCB Log messages and instances
module Plutus.SCB.SCBLogMsg(
    SCBLogMsg(..),
    ContractExeLogMsg(..),
    AppMsg(..)
    ) where

import           Cardano.BM.Data.Tracer             (ToObject (..), TracingVerbosity (..))
import           Cardano.BM.Data.Tracer.Extras      (Tagged (..), mkObjectStr)
import           Data.Aeson                         (FromJSON, ToJSON, Value)
import qualified Data.Aeson.Encode.Pretty           as JSON
import qualified Data.ByteString.Lazy.Char8         as BSL8
import           Data.String                        (IsString (..))
import           Data.Text                          (Text)
import           Data.Text.Prettyprint.Doc          (Pretty (..), colon, hang, viaShow, vsep, (<+>))
import           Data.Time.Units                    (Second)
import           GHC.Generics                       (Generic)
import           Language.Plutus.Contract.State     (ContractRequest)
import           Ledger.Tx                          (Tx)
import           Plutus.SCB.Core                    (CoreMsg (..))
import           Plutus.SCB.Core.ContractInstance   (ContractInstanceMsg (..))
import           Plutus.SCB.Effects.ContractRuntime (ContractRuntimeMsg)
import           Plutus.SCB.Events.Contract         (ContractInstanceId, ContractInstanceState)
import           Plutus.SCB.Instances               ()
import           Plutus.SCB.MonadLoggerBridge       (MonadLoggerMsg (..))
import           Plutus.SCB.ParseStringifiedJSON    (UnStringifyJSONLog (..))
import           Plutus.SCB.Types                   (ContractExe, SCBError (..))
import           Plutus.SCB.Webserver.Types         (WebSocketLogMsg)
import           Wallet.Emulator.Wallet             (WalletEvent (..))

data AppMsg =
    InstalledContractsMsg
    | ActiveContractsMsg
    | TransactionHistoryMsg
    | ContractHistoryMsg
    | ProcessInboxMsg
    | ProcessAllOutboxesMsg Second
    | SCBMsg SCBLogMsg
    | InstalledContract Text
    | ContractInstance ContractExe [ContractInstanceId]
    | TxHistoryItem Tx
    | ContractHistoryItem Int (ContractInstanceState ContractExe) -- index
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty AppMsg where
    pretty = \case
        InstalledContractsMsg -> "Installed contracts"
        ActiveContractsMsg -> "Active contracts"
        TransactionHistoryMsg -> "Transaction history"
        ContractHistoryMsg -> "Contract history"
        ProcessInboxMsg -> "Process contract inbox"
        ProcessAllOutboxesMsg s -> "Processing contract outboxes every" <+> pretty (fromIntegral @_ @Double s) <+> "seconds"
        SCBMsg m -> pretty m
        InstalledContract t -> pretty t
        ContractInstance t s -> pretty t <+> pretty s-- FIXME
        TxHistoryItem t -> pretty t
        ContractHistoryItem i s -> pretty i <> colon <+> pretty s

data SCBLogMsg =
    SContractExeLogMsg ContractExeLogMsg
    | SContractInstanceMsg (ContractInstanceMsg ContractExe)
    | SCoreMsg (CoreMsg ContractExe)
    | SUnstringifyJSON UnStringifyJSONLog
    | SWalletEvent Wallet.Emulator.Wallet.WalletEvent
    | SLoggerBridge MonadLoggerMsg
    | SWebsocketMsg WebSocketLogMsg
    | SContractRuntimeMsg ContractRuntimeMsg
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty SCBLogMsg where
    pretty = \case
        SContractExeLogMsg m   -> pretty m
        SContractInstanceMsg m -> pretty m
        SCoreMsg m             -> pretty m
        SUnstringifyJSON m     -> pretty m
        SWalletEvent w         -> pretty w
        SLoggerBridge m        -> pretty m
        SWebsocketMsg m        -> pretty m
        SContractRuntimeMsg m  -> pretty m

data ContractExeLogMsg =
    InvokeContractMsg
    | InitContractMsg FilePath
    | UpdateContractMsg FilePath (ContractRequest Value)
    | ExportSignatureMsg FilePath
    | ProcessExitFailure String
    | ContractResponse String
    | Migrating
    | InvokingEndpoint String Value
    | EndpointInvocationResponse [Text]
    | ContractExeSCBError SCBError
    | StartingSCBBackendServer Int
    | StartingMetadataServer Int
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty ContractExeLogMsg where
    pretty = \case
        InvokeContractMsg -> "InvokeContract"
        InitContractMsg fp -> fromString fp <+> "init"
        UpdateContractMsg fp vl ->
            let pl = BSL8.unpack (JSON.encodePretty vl) in
            fromString fp
            <+> "update"
            <+> fromString pl
        ExportSignatureMsg fp -> fromString fp <+> "export-signature"
        ProcessExitFailure err -> "ExitFailure" <+> pretty err
        ContractResponse str -> pretty str
        Migrating -> "Migrating"
        InvokingEndpoint s v ->
            "Invoking:" <+> pretty s <+> "/" <+> viaShow v
        EndpointInvocationResponse v ->
            hang 2 $ vsep ("Invocation response:" : fmap pretty v)
        ContractExeSCBError e ->
            "SCB error:" <+> pretty e
        StartingSCBBackendServer port ->
            "Starting SCB backend server on port:" <+> pretty port
        StartingMetadataServer port ->
            "Starting metadata server on port:" <+> pretty port

{- ToObject instances

'ToObject.toObject' is very similar to 'ToJSON.toJSON' except that

* 'toObject' has an additional paramter for verbosity
* 'toObject' must always produce a JSON object (key-value map)

In the definitions below, every object produced by 'toObject' has a field
'string' with a friendly description of the message, similar to its
'Pretty' instance. Additional fields depend on the type of message.

-}

instance ToObject AppMsg where
    toObject v = \case
        InstalledContractsMsg ->
            mkObjectStr "Listing installed contracts" ()
        ActiveContractsMsg ->
            mkObjectStr "Listing active contract instances" ()
        TransactionHistoryMsg ->
            mkObjectStr "Showing transaction history" ()
        ContractHistoryMsg ->
            mkObjectStr "Showing contract history" ()
        ProcessInboxMsg ->
            mkObjectStr "Processing inbox message" ()
        ProcessAllOutboxesMsg second ->
            mkObjectStr "Processing outbox messages"
              (Tagged @"interval_seconds" $ fromIntegral @_ @Integer second)
        SCBMsg m -> toObject v m
        InstalledContract t ->
            mkObjectStr "Installed contract" t
        ContractInstance exe ids ->
            mkObjectStr
                "Active instances for contract"
                (exe, Tagged @"instances" ids)
        TxHistoryItem tx ->
            mkObjectStr "Tx history item" $
                case v of
                    MaximalVerbosity -> Left tx
                    _                -> Right ()
        ContractHistoryItem i state ->
            mkObjectStr "Contract history item" $
                case v of
                    MaximalVerbosity -> Left (Tagged @"index" i, state)
                    _                -> Right (Tagged @"index" i)

instance ToObject SCBLogMsg where
    toObject v = \case
        SContractExeLogMsg m   -> toObject v m
        SContractInstanceMsg m -> toObject v m
        SCoreMsg m             -> toObject v m
        SUnstringifyJSON m     -> toObject v m
        SWalletEvent e         -> toObject v e
        SLoggerBridge e        -> toObject v e
        SWebsocketMsg e        -> toObject v e
        SContractRuntimeMsg e  -> toObject v e

instance ToObject ContractExeLogMsg where
    toObject v = \case
        InvokeContractMsg -> mkObjectStr "invoking contract" ()
        InitContractMsg fp ->
            mkObjectStr "Initialising contract" (Tagged @"file_path" fp)
        UpdateContractMsg fp rq ->
            let f =  Tagged @"file_path" fp in
            mkObjectStr "updating contract" $ case v of
                MaximalVerbosity -> Left (f, rq)
                _                -> Right f
        ExportSignatureMsg fp ->
            mkObjectStr "exporting signature" (Tagged @"file_path" fp)
        ProcessExitFailure f ->
            mkObjectStr "process exit failure" (Tagged @"error" f)
        ContractResponse r ->
            mkObjectStr "received contract response" $
                case v of
                    MaximalVerbosity -> Left (Tagged @"response" r)
                    _                -> Right ()
        Migrating -> mkObjectStr "migrating database" ()
        InvokingEndpoint ep vl ->
            mkObjectStr "Invoking endpoint" $
                case v of
                    MinimalVerbosity -> Left (Tagged @"endpoint" ep)
                    _                -> Right (Tagged @"endpoint" ep, Tagged @"argument" vl)
        EndpointInvocationResponse lns ->
            mkObjectStr "endpoint invocation response"  (Tagged @"reponse" lns)
        ContractExeSCBError err ->
            mkObjectStr "contract executable error" (Tagged @"error" err)
        StartingSCBBackendServer i ->
            mkObjectStr "starting SCB backend server" (Tagged @"port" i)
        StartingMetadataServer i ->
            mkObjectStr "starting SCB metadata server" (Tagged @"port" i)
