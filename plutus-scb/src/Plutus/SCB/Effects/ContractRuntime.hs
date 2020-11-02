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
module Plutus.SCB.Effects.ContractRuntime(
    ContractRuntimeMsg(..)
    , handleContractRuntime
    ) where

import           Cardano.BM.Data.Tracer           (ToObject (..), TracingVerbosity (..))
import           Cardano.BM.Data.Tracer.Extras    (Tagged (..), mkObjectStr)
import           Control.Monad.Freer              (Eff, Member, type (~>))
import           Control.Monad.Freer.Error        (runError)
import           Control.Monad.Freer.Extra.Log    (LogMsg)
import           Control.Monad.Freer.Log          (logInfo, logWarn)
import qualified Data.Aeson                       as JSON
import           Data.Text.Prettyprint.Doc        (Pretty (..), (<+>))
import           GHC.Generics                     (Generic)
import           Language.Plutus.Contract.Trace   (EndpointError, toNotifyError)
import           Plutus.SCB.Core.ContractInstance (ContractInstanceMsg)
import qualified Plutus.SCB.Core.ContractInstance as Instance
import           Plutus.SCB.Effects.EventLog      (EventLogEffect)
import           Plutus.SCB.Events                (ChainEvent)
import           Wallet.Effects                   (ContractRuntimeEffect (..))
import           Wallet.Types                     (EndpointDescription (..), Notification (..), NotificationError)

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
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member (LogMsg (ContractInstanceMsg t)) effs
    , Member (LogMsg ContractRuntimeMsg) effs
    )
    => ContractRuntimeEffect
    ~> Eff effs
handleContractRuntime = \case
    SendNotification n@Notification{notificationContractID, notificationContractEndpoint=EndpointDescription nm, notificationContractArg} -> do
        logInfo $ SendingNotification n
        r <- runError @EndpointError
                $ Instance.callContractEndpoint' @t
                    notificationContractID
                    nm
                    notificationContractArg
        case r of
            Left err -> do
                let e = toNotifyError notificationContractID err
                logWarn $ NotificationFailure e
                pure $ Just e
            Right _ -> do
                logInfo $ NotificationSuccess n
                pure Nothing
