{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

-- | PAB Log messages and instances
module Plutus.PAB.Monitoring.PABLogMsg(
    PABLogMsg(..),
    ChainIndexServerMsg,
    WalletMsg,
    MockServerLogMsg,
    AppMsg(..),
    CoreMsg(..),
    PABMultiAgentMsg(..),
    RequestSize(..)
    ) where

import           Data.Aeson                       (FromJSON, ToJSON, Value)
import           Data.Text                        (Text)
import           Data.Text.Prettyprint.Doc        (Pretty (..), colon, viaShow, (<+>))
import           GHC.Generics                     (Generic)

import           Cardano.BM.Data.Tracer           (ToObject (..), TracingVerbosity (..))
import           Cardano.BM.Data.Tracer.Extras    (StructuredLog, Tagged (..), mkObjectStr)
import           Cardano.ChainIndex.Types         (ChainIndexServerMsg)
import           Cardano.Node.Types               (MockServerLogMsg)
import           Cardano.Wallet.Mock.Types        (WalletMsg)
import           Data.Aeson.Text                  (encodeToLazyText)
import qualified Data.Text                        as T
import           Plutus.Contract.Effects          (PABReq, PABResp)
import           Plutus.Contract.Resumable        (Response)
import           Plutus.Contract.State            (ContractResponse)
import           Plutus.PAB.Core.ContractInstance (ContractInstanceMsg (..))
import           Plutus.PAB.Effects.Contract      (PABContract (..))
import           Plutus.PAB.Events.Contract       (ContractInstanceId)
import           Plutus.PAB.Instances             ()
import           Wallet.Emulator.LogMessages      (TxBalanceMsg)
import           Wallet.Emulator.MultiAgent       (EmulatorEvent)
import           Wallet.Emulator.Wallet           (Wallet)

data AppMsg t =
    ActiveContractsMsg
    | ContractHistoryMsg
    | PABMsg (PABLogMsg t)
    | AvailableContract Text
    | ContractInstances (ContractDef t) [ContractInstanceId]
    | ContractHistoryItem ContractInstanceId (Response PABResp)
    deriving stock (Generic)

deriving stock instance (Show (ContractDef t)) => Show (AppMsg t)
deriving anyclass instance (ToJSON (ContractDef t)) => ToJSON (AppMsg t)
deriving anyclass instance (FromJSON (ContractDef t)) => FromJSON (AppMsg t)

instance (Pretty (ContractDef t)) => Pretty (AppMsg t) where
    pretty = \case
        ActiveContractsMsg               -> "Active contracts"
        ContractHistoryMsg               -> "Contract history"
        PABMsg m                         -> pretty m
        AvailableContract t              -> pretty t
        ContractInstances t s            -> pretty t <+> pretty s
        ContractHistoryItem instanceId s -> pretty instanceId <> colon <+> pretty (fmap encodeToLazyText s)

data PABLogMsg t =
    SCoreMsg (CoreMsg t)
    | SChainIndexServerMsg ChainIndexServerMsg
    | SWalletMsg WalletMsg
    | SMockserverLogMsg MockServerLogMsg
    | SMultiAgent (PABMultiAgentMsg t)
    deriving stock (Generic)

deriving stock instance (Show (ContractDef t)) => Show (PABLogMsg t)
deriving anyclass instance (ToJSON (ContractDef t)) => ToJSON (PABLogMsg t)
deriving anyclass instance (FromJSON (ContractDef t)) => FromJSON (PABLogMsg t)

instance Pretty (ContractDef t) => Pretty (PABLogMsg t) where
    pretty = \case
        SCoreMsg m             -> pretty m
        SChainIndexServerMsg m -> pretty m
        SWalletMsg m           -> pretty m
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

instance (ToJSON (ContractDef t), StructuredLog (ContractDef t)) => ToObject (AppMsg t) where
    toObject v = \case
        ActiveContractsMsg ->
            mkObjectStr "Listing active contract instances" ()
        ContractHistoryMsg ->
            mkObjectStr "Showing contract history" ()
        PABMsg m -> toObject v m
        AvailableContract t ->
            mkObjectStr "Available contract" t
        ContractInstances exe ids ->
            mkObjectStr
                "Active instances for contract"
                (exe, Tagged @"instances" ids)
        ContractHistoryItem i state ->
            mkObjectStr "Contract history item" $
                case v of
                    MaximalVerbosity -> Left (i, state)
                    _                -> Right i

instance (StructuredLog (ContractDef t), ToJSON (ContractDef t)) => ToObject (PABLogMsg t) where
    toObject v = \case
        SCoreMsg m             -> toObject v m
        SChainIndexServerMsg m -> toObject v m
        SWalletMsg m           -> toObject v m
        SMockserverLogMsg m    -> toObject v m
        SMultiAgent m          -> toObject v m

-- | FIXME: Redundant?
data PABMultiAgentMsg t =
    EmulatorMsg EmulatorEvent
    | ContractInstanceLog (ContractInstanceMsg t)
    | UserLog T.Text
    | SqlLog String
    | PABStateRestored Int
    | RestoringPABState
    | StartingPABBackendServer Int
    | WalletBalancingMsg Wallet TxBalanceMsg
    deriving stock Generic

instance (StructuredLog (ContractDef t), ToJSON (ContractDef t)) => ToObject (PABMultiAgentMsg t) where
    toObject v = \case
        EmulatorMsg e              -> mkObjectStr "emulator message" (Tagged @"payload" e)
        ContractInstanceLog m      -> toObject v m
        UserLog t                  -> toObject v t
        SqlLog s                   -> toObject v s
        RestoringPABState          -> mkObjectStr "Restoring PAB state ..." ()
        PABStateRestored n         -> mkObjectStr ( "PAB state restored with "
                                                 <> T.pack (show n)
                                                 <> " contract instance(s)."
                                                  ) ()
        StartingPABBackendServer i -> mkObjectStr "starting backend server" (Tagged @"port" i)
        WalletBalancingMsg w m     -> mkObjectStr "balancing" (Tagged @"wallet" w, Tagged @"message" m)

deriving stock instance (Show (ContractDef t)) => Show (PABMultiAgentMsg t)
deriving anyclass instance (ToJSON (ContractDef t)) => ToJSON (PABMultiAgentMsg t)
deriving anyclass instance (FromJSON (ContractDef t)) => FromJSON (PABMultiAgentMsg t)

instance Pretty (ContractDef t) => Pretty (PABMultiAgentMsg t) where
    pretty = \case
        EmulatorMsg m         -> pretty m
        ContractInstanceLog m -> pretty m
        UserLog m             -> pretty m
        SqlLog m              -> pretty m
        RestoringPABState     -> "Restoring PAB state ..."
        PABStateRestored 0    -> "No constract instance were restored in the PAB state."
        PABStateRestored 1    -> "PAB state restored with 1 contract instance."
        PABStateRestored n    -> "PAB state restored with"
                              <+> pretty n
                              <+> "contract instances."
        StartingPABBackendServer port ->
            "Starting PAB backend server on port:" <+> pretty port
        WalletBalancingMsg w m -> pretty w <> colon <+> pretty m

data CoreMsg t =
    FindingContract ContractInstanceId
    | FoundContract (Maybe (ContractResponse Value Value PABResp PABReq))
    | ConnectingToAlonzoNode
    deriving stock Generic

deriving stock instance (Show (ContractDef t)) => Show (CoreMsg t)
deriving anyclass instance (ToJSON (ContractDef t)) => ToJSON (CoreMsg t)
deriving anyclass instance (FromJSON (ContractDef t)) => FromJSON (CoreMsg t)

instance Pretty (ContractDef t) => Pretty (CoreMsg t) where
    pretty = \case
        FindingContract i      -> "Finding contract" <+> pretty i
        FoundContract c        -> "Found contract" <+> viaShow c
        ConnectingToAlonzoNode -> "Connecting to Alonzo node"

instance (StructuredLog (ContractDef t), ToJSON (ContractDef t)) => ToObject (CoreMsg t) where
    toObject v = \case
        FindingContract instanceID ->
            mkObjectStr "finding contract instance" instanceID
        FoundContract state ->
            mkObjectStr "found contract" $
                case v of
                    MaximalVerbosity -> Left (Tagged @"contract" state)
                    _                -> Right ()
        ConnectingToAlonzoNode -> mkObjectStr "Connecting to Alonzo node" ()

newtype RequestSize = RequestSize Int
    deriving stock (Show)
    deriving newtype (ToJSON, FromJSON)

instance Pretty RequestSize where
    pretty (RequestSize i) = pretty i <+> "bytes"
