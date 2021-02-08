{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

-- | PAB Log messages and instances
module Plutus.PAB.PABLogMsg(
    PABLogMsg(..),
    ContractExeLogMsg(..),
    ChainIndexServerMsg(..),
    SigningProcessMsg,
    AppMsg(..)
    ) where

import           Data.Aeson                         (FromJSON, ToJSON, Value)
import qualified Data.Aeson.Encode.Pretty           as JSON
import qualified Data.ByteString.Lazy.Char8         as BSL8
import           Data.String                        (IsString (..))
import           Data.Text                          (Text)
import           Data.Text.Prettyprint.Doc          (Pretty (..), colon, hang, parens, viaShow, vsep, (<+>))
import           Data.Time.Units                    (Second)
import           GHC.Generics                       (Generic)

import           Cardano.BM.Data.Tracer             (ToObject (..), TracingVerbosity (..))
import           Cardano.BM.Data.Tracer.Extras      (Tagged (..), mkObjectStr)
import           Cardano.Node.Types                 (FollowerID)
import           Cardano.SigningProcess.Types       (SigningProcessMsg)
import           Language.Plutus.Contract.State     (ContractRequest)
import           Ledger.Tx                          (Tx)
import           Plutus.PAB.Core                    (CoreMsg (..))
import           Plutus.PAB.Core.ContractInstance   (ContractInstanceMsg (..))
import           Plutus.PAB.Effects.ContractRuntime (ContractRuntimeMsg)
import           Plutus.PAB.Events.Contract         (ContractInstanceId, ContractInstanceState)
import           Plutus.PAB.Instances               ()
import           Plutus.PAB.MonadLoggerBridge       (MonadLoggerMsg (..))
import           Plutus.PAB.ParseStringifiedJSON    (UnStringifyJSONLog (..))
import           Plutus.PAB.Types                   (ContractExe, PABError (..))
import           Plutus.PAB.Webserver.Types         (WebSocketLogMsg)
import           Wallet.Emulator.Wallet             (WalletEvent (..))

data AppMsg =
    InstalledContractsMsg
    | ActiveContractsMsg
    | TransactionHistoryMsg
    | ContractHistoryMsg
    | ProcessInboxMsg
    | ProcessAllOutboxesMsg Second
    | PABMsg PABLogMsg
    | InstalledContract Text
    | ContractInstance ContractExe [ContractInstanceId]
    | TxHistoryItem Tx
    | ContractHistoryItem Int (ContractInstanceState ContractExe)
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

-- | Messages from the ChainIndex Server
data ChainIndexServerMsg =
    -- | Obtaining a new follower
    ObtainingFollowerID
    -- | Obtained a new follower 'FollowerID'
    | ObtainedFollowerID FollowerID
    -- | Updating the chain index with 'FollowerID'
    | UpdatingChainIndex FollowerID
    -- | Requesting new blocks from the node
    | AskingNodeForNewBlocks
    -- | Requesting the current slot from the node
    | AskingNodeForCurrentSlot
    -- | Starting a node client thread
    | StartingNodeClientThread
    -- | Starting ChainIndex service
    | StartingChainIndex
        Int    -- ^ Port number
      -- | Received transaction
    | ReceivedBlocksTxns
        Int    -- ^ Blocks
        Int    -- ^ Transactions
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty ChainIndexServerMsg where
    pretty = \case
        ObtainingFollowerID -> "Obtaining follower ID"
        ObtainedFollowerID i -> "Obtained follower ID:" <+> pretty i
        UpdatingChainIndex i -> "Updating chain index with follower ID" <+> pretty i
        ReceivedBlocksTxns blocks txns -> "Received" <+> pretty blocks <+> "blocks" <+> parens (pretty txns <+> "transactions")
        AskingNodeForNewBlocks -> "Asking the node for new blocks"
        AskingNodeForCurrentSlot -> "Asking the node for the current slot"
        StartingNodeClientThread -> "Starting node client thread"
        StartingChainIndex port -> "Starting chain index on port: " <> pretty port

instance Pretty AppMsg where
    pretty = \case
        InstalledContractsMsg -> "Installed contracts"
        ActiveContractsMsg -> "Active contracts"
        TransactionHistoryMsg -> "Transaction history"
        ContractHistoryMsg -> "Contract history"
        ProcessInboxMsg -> "Process contract inbox"
        ProcessAllOutboxesMsg s -> "Processing contract outboxes every" <+> pretty (fromIntegral @_ @Double s) <+> "seconds"
        PABMsg m -> pretty m
        InstalledContract t -> pretty t
        ContractInstance t s -> pretty t <+> pretty s-- FIXME
        TxHistoryItem t -> pretty t
        ContractHistoryItem i s -> pretty i <> colon <+> pretty s

data PABLogMsg =
    SContractExeLogMsg ContractExeLogMsg
    | SContractInstanceMsg (ContractInstanceMsg ContractExe)
    | SCoreMsg (CoreMsg ContractExe)
    | SUnstringifyJSON UnStringifyJSONLog
    | SWalletEvent Wallet.Emulator.Wallet.WalletEvent
    | SLoggerBridge MonadLoggerMsg
    | SWebsocketMsg WebSocketLogMsg
    | SContractRuntimeMsg ContractRuntimeMsg
    | SChainIndexServerMsg ChainIndexServerMsg
    | SSigningProcessMsg SigningProcessMsg
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty PABLogMsg where
    pretty = \case
        SContractExeLogMsg m   -> pretty m
        SContractInstanceMsg m -> pretty m
        SCoreMsg m             -> pretty m
        SUnstringifyJSON m     -> pretty m
        SWalletEvent w         -> pretty w
        SLoggerBridge m        -> pretty m
        SWebsocketMsg m        -> pretty m
        SContractRuntimeMsg m  -> pretty m
        SChainIndexServerMsg m -> pretty m
        SSigningProcessMsg m   -> pretty m


-- | Messages from the Signing Process

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
    | ContractExePABError PABError
    | StartingPABBackendServer Int
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
        ContractExePABError e ->
            "PAB error:" <+> pretty e
        StartingPABBackendServer port ->
            "Starting PAB backend server on port:" <+> pretty port
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
        PABMsg m -> toObject v m
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

instance ToObject PABLogMsg where
    toObject v = \case
        SContractExeLogMsg m   -> toObject v m
        SContractInstanceMsg m -> toObject v m
        SCoreMsg m             -> toObject v m
        SUnstringifyJSON m     -> toObject v m
        SWalletEvent e         -> toObject v e
        SLoggerBridge e        -> toObject v e
        SWebsocketMsg e        -> toObject v e
        SContractRuntimeMsg e  -> toObject v e
        SChainIndexServerMsg m -> toObject v m
        SSigningProcessMsg m   -> toObject v m


instance ToObject ChainIndexServerMsg where
    toObject _ = \case
      ObtainingFollowerID      -> mkObjectStr "obtaining FollowerID" ()
      ObtainedFollowerID fID   -> mkObjectStr "obtained FollowerID" (Tagged @"followerID" fID)
      UpdatingChainIndex fID   -> mkObjectStr "updating chainIndex with FollowerID" (Tagged @"followerID" fID)
      ReceivedBlocksTxns x y   -> mkObjectStr "received block transactions" (Tagged @"blocks" x, Tagged @"transactions" y)
      AskingNodeForNewBlocks   -> mkObjectStr "asking for new blocks" ()
      AskingNodeForCurrentSlot -> mkObjectStr "asking node for current slot" ()
      StartingNodeClientThread -> mkObjectStr "starting node client thread" ()
      StartingChainIndex p     -> mkObjectStr "starting chain index" (Tagged @"port" p)


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
        ContractExePABError err ->
            mkObjectStr "contract executable error" (Tagged @"error" err)
        StartingPABBackendServer i ->
            mkObjectStr "starting PAB backend server" (Tagged @"port" i)
        StartingMetadataServer i ->
            mkObjectStr "starting PAB metadata server" (Tagged @"port" i)
