{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

-- | PAB Log messages and instances
module Plutus.PAB.Monitoring.PABLogMsg(
    PABLogMsg(..),
    ContractExeLogMsg(..),
    ChainIndexServerMsg,
    MetadataLogMessage,
    WalletMsg,
    MockServerLogMsg,
    AppMsg(..),
    CoreMsg(..),
    PABMultiAgentMsg(..),
    ContractEffectMsg(..)
    ) where

import           Data.Aeson                              (FromJSON, ToJSON)
import qualified Data.Aeson as JSON
import           Data.Text                               (Text)
import           Data.Text.Prettyprint.Doc               (Pretty (..), colon, (<+>))
import           GHC.Generics                            (Generic)

import           Cardano.BM.Data.Tracer                  (ToObject (..), TracingVerbosity (..))
import           Cardano.BM.Data.Tracer.Extras           (Tagged (..), mkObjectStr, StructuredLog)
import           Cardano.ChainIndex.Types                (ChainIndexServerMsg)
import           Cardano.Metadata.Types                  (MetadataLogMessage)
import           Cardano.Node.Types                      (MockServerLogMsg)
import           Cardano.Wallet.Types                    (WalletMsg)
import           Data.Aeson.Text                         (encodeToLazyText)
import qualified Data.Text                               as T
import           Plutus.Contract.Resumable      (Response)
import           Plutus.Contract.State          (ContractRequest)
import           Plutus.PAB.Core.ContractInstance        (ContractInstanceMsg (..))
import           Plutus.PAB.Effects.Contract             (PABContract (..))
import           Plutus.PAB.Effects.Contract.ContractExe (ContractExe, ContractExeLogMsg (..))
import           Plutus.PAB.Effects.ContractRuntime      (ContractRuntimeMsg)
import           Plutus.PAB.Events.Contract              (ContractInstanceId, ContractPABRequest)
import           Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse)
import           Plutus.PAB.Instances                    ()
import           Plutus.PAB.Monitoring.MonadLoggerBridge (MonadLoggerMsg (..))
import           Plutus.PAB.ParseStringifiedJSON         (UnStringifyJSONLog (..))
import           Wallet.Emulator.MultiAgent              (EmulatorEvent)
import           Wallet.Emulator.Wallet                  (WalletEvent (..))

data AppMsg t =
    InstalledContractsMsg
    | ActiveContractsMsg
    | ContractHistoryMsg
    | PABMsg PABLogMsg
    | InstalledContract Text
    | ContractInstances (ContractDef t) [ContractInstanceId]
    | ContractHistoryItem ContractInstanceId (Response JSON.Value)
    deriving stock (Generic)

deriving stock instance (Show (ContractDef t)) => Show (AppMsg t)
deriving anyclass instance (ToJSON (ContractDef t)) => ToJSON (AppMsg t)
deriving anyclass instance (FromJSON (ContractDef t)) => FromJSON (AppMsg t)

instance Pretty (ContractDef t) => Pretty (AppMsg t) where
    pretty = \case
        InstalledContractsMsg            -> "Installed contracts"
        ActiveContractsMsg               -> "Active contracts"
        ContractHistoryMsg               -> "Contract history"
        PABMsg m                         -> pretty m
        InstalledContract t              -> pretty t
        ContractInstances t s            -> pretty t <+> pretty s
        ContractHistoryItem instanceId s -> pretty instanceId <> colon <+> pretty (fmap encodeToLazyText s)

data PABLogMsg =
    SContractExeLogMsg ContractExeLogMsg
    | SContractInstanceMsg (ContractInstanceMsg ContractExe)
    | SCoreMsg (CoreMsg ContractExe)
    | SUnstringifyJSON UnStringifyJSONLog
    | SWalletEvent Wallet.Emulator.Wallet.WalletEvent
    | SLoggerBridge MonadLoggerMsg
    | SContractRuntimeMsg ContractRuntimeMsg
    | SChainIndexServerMsg ChainIndexServerMsg
    | SWalletMsg WalletMsg
    | SMetaDataLogMsg MetadataLogMessage
    | SMockserverLogMsg MockServerLogMsg
    | SMultiAgent (PABMultiAgentMsg ContractExe)
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
        SContractRuntimeMsg m  -> pretty m
        SChainIndexServerMsg m -> pretty m
        SWalletMsg m           -> pretty m
        SMetaDataLogMsg m      -> pretty m
        SMockserverLogMsg m    -> pretty m
        SMultiAgent m          -> pretty m



{- ToObject instances

'ToObject.toObject' is very similar to 'ToJSON.toJSON' except that

* 'toObject' has an additional paramter for verbosity
* 'toObject' must always produce a JSON object (key-value map)

In the definitions below, every object produced by 'toObject' has a field
'string' with a friendly description of the message, similar to its
'Pretty' instance. Additional fields depend on the type of message.

-}

instance StructuredLog (ContractDef t) => ToObject (AppMsg t) where
    toObject v = \case
        InstalledContractsMsg ->
            mkObjectStr "Listing installed contracts" ()
        ActiveContractsMsg ->
            mkObjectStr "Listing active contract instances" ()
        ContractHistoryMsg ->
            mkObjectStr "Showing contract history" ()
        PABMsg m -> toObject v m
        InstalledContract t ->
            mkObjectStr "Installed contract" t
        ContractInstances exe ids ->
            mkObjectStr
                "Active instances for contract"
                (exe, Tagged @"instances" ids)
        ContractHistoryItem i state ->
            mkObjectStr "Contract history item" $
                case v of
                    MaximalVerbosity -> Left (i, state)
                    _                -> Right i

instance ToObject PABLogMsg where
    toObject v = \case
        SContractExeLogMsg m   -> toObject v m
        SContractInstanceMsg m -> toObject v m
        SCoreMsg m             -> toObject v m
        SUnstringifyJSON m     -> toObject v m
        SWalletEvent e         -> toObject v e
        SLoggerBridge e        -> toObject v e
        SContractRuntimeMsg e  -> toObject v e
        SChainIndexServerMsg m -> toObject v m
        SWalletMsg m           -> toObject v m
        SMetaDataLogMsg m      -> toObject v m
        SMockserverLogMsg m    -> toObject v m
        SMultiAgent m          -> toObject v m

-- | FIXME: Redundant?
data PABMultiAgentMsg t =
    EmulatorMsg EmulatorEvent
    | ContractMsg ContractEffectMsg
    | MetadataLog MetadataLogMessage
    | ChainIndexServerLog ChainIndexServerMsg
    | ContractInstanceLog (ContractInstanceMsg t)
    | CoreLog (CoreMsg t)
    | RuntimeLog ContractRuntimeMsg
    | UserLog T.Text
    | StartingPABBackendServer Int
    | StartingMetadataServer Int
    deriving stock Generic

instance (StructuredLog t, ToJSON t, ToJSON (State t), ToJSON (ContractDef t)) => ToObject (PABMultiAgentMsg t) where
    toObject v = \case
        EmulatorMsg e              -> mkObjectStr "emulator message" (Tagged @"payload" e)
        ContractMsg e              -> mkObjectStr "contract message" (Tagged @"payload" e)
        MetadataLog m              -> toObject v m
        ChainIndexServerLog m      -> toObject v m
        ContractInstanceLog m      -> toObject v m
        CoreLog m                  -> toObject v m
        RuntimeLog m               -> toObject v m
        UserLog t                  -> toObject v t
        StartingPABBackendServer i -> mkObjectStr "starting backend server" (Tagged @"port" i)
        StartingMetadataServer i   -> mkObjectStr "starting backend server" (Tagged @"port" i)

deriving stock instance (Show t, Show (ContractDef t), Show (State t)) => Show (PABMultiAgentMsg t)
deriving anyclass instance (ToJSON t, ToJSON (ContractDef t), ToJSON (State t)) => ToJSON (PABMultiAgentMsg t)
deriving anyclass instance (FromJSON t, FromJSON (ContractDef t), FromJSON (State t)) => FromJSON (PABMultiAgentMsg t)

instance (Pretty (ContractDef t), Pretty t, Pretty (State t)) => Pretty (PABMultiAgentMsg t) where
    pretty = \case
        EmulatorMsg m         -> pretty m
        ContractMsg m         -> pretty m
        MetadataLog m         -> pretty m
        ChainIndexServerLog m -> pretty m
        ContractInstanceLog m -> pretty m
        CoreLog m             -> pretty m
        RuntimeLog m          -> pretty m
        UserLog m             -> pretty m
        StartingPABBackendServer port ->
            "Starting PAB backend server on port:" <+> pretty port
        StartingMetadataServer port ->
            "Starting metadata server on port:" <+> pretty port

data CoreMsg t =
    Installing t
    | Installed
    | FindingContract ContractInstanceId
    | FoundContract (Maybe (PartiallyDecodedResponse ContractPABRequest))
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty t => Pretty (CoreMsg t) where
    pretty = \case
        Installing d      -> "Installing" <+> pretty d
        Installed         -> "Installed"
        FindingContract i -> "Finding contract" <+> pretty i
        FoundContract c   -> "Found contract" <+> pretty c

instance (StructuredLog t, ToJSON t) => ToObject (CoreMsg t) where
    toObject v = \case
        Installing t ->
            mkObjectStr "installing contract" t
        Installed ->
            mkObjectStr "contract installed" ()
        FindingContract instanceID ->
            mkObjectStr "finding contract instance" instanceID
        FoundContract state ->
            mkObjectStr "found contract" $
                case v of
                    MaximalVerbosity -> Left state
                    _                -> Right ()

data ContractEffectMsg =
    SendContractRequest (ContractRequest JSON.Value)
    | ReceiveContractResponse (PartiallyDecodedResponse ContractPABRequest)
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty ContractEffectMsg where
    pretty = \case
        SendContractRequest vl      -> "Request:" <+> pretty vl
        ReceiveContractResponse rsp -> "Response:" <+> pretty rsp
