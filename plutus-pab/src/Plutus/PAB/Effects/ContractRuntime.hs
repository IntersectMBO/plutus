{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE StrictData          #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Plutus.PAB.Effects.ContractRuntime(
    ContractRuntimeMsg(..)
    , handleContractRuntime
    ) where

import           Cardano.BM.Data.Tracer               (ToObject (..), TracingVerbosity (..))
import           Cardano.BM.Data.Tracer.Extras        (Tagged (..), mkObjectStr)
import qualified Control.Concurrent.STM               as STM
import           Control.Monad.Freer                  (Eff, LastMember, Member, type (~>))
import           Control.Monad.Freer.Error            (runError)
import           Control.Monad.Freer.Extras.Log       (LogMsg, logInfo, logWarn)
import           Control.Monad.Freer.Reader           (Reader, ask)
import           Control.Monad.IO.Class               (MonadIO (..))
import qualified Data.Aeson                           as JSON
import           Data.Text.Prettyprint.Doc            (Pretty (..), (<+>))
import           GHC.Generics                         (Generic)
import           Plutus.Contract.Trace       (EndpointError, toNotifyError)
import           Plutus.PAB.Core.ContractInstance     (ContractInstanceMsg)
import qualified Plutus.PAB.Core.ContractInstance     as Instance
import           Plutus.PAB.Core.ContractInstance.STM (InstancesState)
import           Plutus.PAB.Effects.EventLog          (EventLogEffect)
import           Plutus.PAB.Events                    (ChainEvent)
import           Wallet.Effects                       (ContractRuntimeEffect (..))
import           Wallet.Types                         (EndpointDescription (..), Notification (..), NotificationError)

data ContractRuntimeMsg =
    SendingNotification Notification
    | NotificationSuccess Notification
    | NotificationFailure NotificationError
    deriving stock (Eq, Show, Generic)
    deriving anyclass (JSON.ToJSON, JSON.FromJSON)

instance ToObject ContractRuntimeMsg where
    toObject v = \case
        SendingNotification Notification{notificationContractID, notificationContractEndpoint, notificationContractArg} ->
            mkObjectStr "Sending notification" $
                case v of
                    MaximalVerbosity -> Left (notificationContractID, notificationContractEndpoint, Tagged @"argument" notificationContractArg)
                    _                -> Right (notificationContractID, notificationContractEndpoint)
        NotificationSuccess Notification{notificationContractID, notificationContractEndpoint, notificationContractArg} ->
            mkObjectStr "Notification successful" $
                case v of
                    MaximalVerbosity -> Left (notificationContractID, notificationContractEndpoint, Tagged @"argument" notificationContractArg)
                    _                -> Right (notificationContractID, notificationContractEndpoint)
        NotificationFailure e ->
            mkObjectStr "Notification failure" (Tagged @"error" e)

instance Pretty ContractRuntimeMsg where
    pretty = \case
        SendingNotification Notification{notificationContractID, notificationContractEndpoint} ->
            "Sending notification" <+> pretty notificationContractID <+> pretty notificationContractEndpoint
        NotificationSuccess _ -> "Notification successful"
        NotificationFailure e -> "Notification failure:" <+> pretty e

handleContractRuntime ::
    forall t m effs.
    ( Member (LogMsg (ContractInstanceMsg t)) effs
    , Member (LogMsg ContractRuntimeMsg) effs
    , Member (Reader InstancesState) effs
    , LastMember m effs
    , MonadIO m
    )
    => ContractRuntimeEffect
    ~> Eff effs
handleContractRuntime = \case
    SendNotification n@Notification{notificationContractID, notificationContractEndpoint=EndpointDescription nm, notificationContractArg} -> do
        logInfo $ SendingNotification n
        env <- ask @InstancesState
        result <- liftIO $ STM.atomically $ Instance.callEndpointOnInstance
                    env
                    (EndpointDescription nm)
                    notificationContractArg
                    notificationContractID
        case result of
            Just err -> do
                logWarn $ NotificationFailure err
                pure $ Just err
            Nothing -> do
                logInfo $ NotificationSuccess n
                pure Nothing
