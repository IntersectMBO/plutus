{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}
-- | Request handlers for contract instance runners.
module Plutus.PAB.Core.ContractInstance.RequestHandlers(
    ContractInstanceMsg(..)
    , processOwnPubkeyRequests
    , processAwaitSlotRequests
    , processUtxoAtRequests
    , processWriteTxRequests
    , processNextTxAtRequests
    , processTxConfirmedRequests
    , processInstanceRequests
    , processNotificationEffects
    -- * Etc.
    , MaxIterations(..)
    , defaultMaxIterations
    ) where

import           Cardano.BM.Data.Tracer                        (ToObject (..), TracingVerbosity (..))
import           Cardano.BM.Data.Tracer.Extras                 (Tagged (Tagged), mkObjectStr)
import           Control.Arrow                                 ((>>>), (>>^))
import           Control.Monad                                 (void)
import           Control.Monad.Freer                           (Member)
import           Control.Monad.Freer.Extras.Log                (LogMessage, LogMsg, LogObserve, logInfo)
import           Control.Monad.Freer.Reader                    (Reader)
import           Data.Aeson                                    (FromJSON, ToJSON)
import qualified Data.Aeson                                    as JSON
import qualified Data.Text                                     as Text
import           Data.Text.Prettyprint.Doc                     (Pretty, parens, pretty, viaShow, (<+>))
import           GHC.Generics                                  (Generic)
import           Plutus.Contract.Effects.AwaitSlot    (WaitingForSlot (..))
import           Plutus.Contract.Effects.WriteTx      (WriteTxResponse (..))
import           Plutus.Contract.Resumable            (IterationID, Request (..), Response (..))
import           Plutus.Contract.Trace.RequestHandler (RequestHandler (..), RequestHandlerLogMsg, extract,
                                                                maybeToHandler)
import qualified Plutus.Contract.Trace.RequestHandler as RequestHandler
import           Ledger.Tx                                     (Tx, txId)
import           Plutus.PAB.Command                            (saveBalancedTx, saveBalancedTxResult)
import qualified Plutus.PAB.Effects.Contract                   as Contract
import           Plutus.PAB.Effects.EventLog                   (EventLogEffect, runCommand)
import           Plutus.PAB.Events                             (ChainEvent)
import           Plutus.PAB.Events.Contract                    (ContractInstanceId (..), ContractPABRequest (..),
                                                                ContractResponse (..), PartiallyDecodedResponse (..))
import qualified Plutus.PAB.Events.Contract                    as Events.Contract
import           Plutus.PAB.Types                              (Source (NodeEventSource, WalletEventSource))
import           Wallet.Effects                                (ChainIndexEffect, ContractRuntimeEffect, WalletEffect)
import           Wallet.Emulator.LogMessages                   (TxBalanceMsg)
import           Wallet.Types                                  (NotificationError)

processOwnPubkeyRequests ::
    forall effs.
    ( Member (LogObserve (LogMessage Text.Text)) effs
    , Member WalletEffect effs
    )
    => RequestHandler effs ContractPABRequest ContractResponse
processOwnPubkeyRequests =
    maybeToHandler (extract Events.Contract._OwnPubkeyRequest) >>>
        fmap OwnPubkeyResponse RequestHandler.handleOwnPubKey

processAwaitSlotRequests ::
    forall effs.
    ( Member (LogObserve (LogMessage Text.Text)) effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    , Member WalletEffect effs
    )
    => RequestHandler effs ContractPABRequest ContractResponse
processAwaitSlotRequests =
    maybeToHandler (fmap unWaitingForSlot . extract Events.Contract._AwaitSlotRequest)
    >>> RequestHandler.handleSlotNotifications
    >>^ AwaitSlotResponse

processUtxoAtRequests ::
    forall effs.
    ( Member ChainIndexEffect effs
    , Member (LogObserve (LogMessage Text.Text)) effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    )
    => RequestHandler effs ContractPABRequest ContractResponse
processUtxoAtRequests =
    maybeToHandler (extract Events.Contract._UtxoAtRequest)
    >>> RequestHandler.handleUtxoQueries
    >>^ UtxoAtResponse

processWriteTxRequests ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member ChainIndexEffect effs
    , Member WalletEffect effs
    , Member (LogObserve (LogMessage Text.Text)) effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    , Member (LogMsg (ContractInstanceMsg t)) effs
    , Member (LogMsg TxBalanceMsg) effs
    )
    => RequestHandler effs ContractPABRequest ContractResponse
processWriteTxRequests =
    let store result = case result of
            Left err -> pure (Left err)
            Right signedTx -> do
                logInfo @(ContractInstanceMsg t) $ StoringSignedTx signedTx
                void $ runCommand (saveBalancedTx @t) WalletEventSource signedTx
                void $ runCommand (saveBalancedTxResult @t) NodeEventSource signedTx
                pure (Right signedTx)
    in

    maybeToHandler (extract Events.Contract._WriteTxRequest)
    >>> RequestHandler.handlePendingTransactions
    >>> RequestHandler store
    >>^ WriteTxResponse . either WriteTxFailed WriteTxSuccess

processNextTxAtRequests ::
    forall effs.
    ( Member (LogObserve (LogMessage Text.Text)) effs
    , Member WalletEffect effs
    , Member ChainIndexEffect effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    )
    => RequestHandler effs ContractPABRequest ContractResponse
processNextTxAtRequests =
    maybeToHandler (extract Events.Contract._NextTxAtRequest)
    >>> RequestHandler.handleNextTxAtQueries
    >>^ NextTxAtResponse

processTxConfirmedRequests ::
    forall effs.
    ( Member ChainIndexEffect effs
    , Member (LogObserve (LogMessage Text.Text)) effs
    )
    => RequestHandler effs ContractPABRequest ContractResponse
processTxConfirmedRequests =
    maybeToHandler (extract Events.Contract._AwaitTxConfirmedRequest)
    >>> RequestHandler.handleTxConfirmedQueries
    >>^ AwaitTxConfirmedResponse

processInstanceRequests ::
    forall effs.
    ( Member (Reader ContractInstanceId) effs
    , Member (LogObserve (LogMessage Text.Text)) effs
    )
    => RequestHandler effs ContractPABRequest ContractResponse
processInstanceRequests =
    maybeToHandler (extract Events.Contract._OwnInstanceIdRequest)
    >>> RequestHandler.handleOwnInstanceIdQueries
    >>^ OwnInstanceResponse

processNotificationEffects ::
    forall effs.
    ( Member ContractRuntimeEffect effs
    , Member (LogObserve (LogMessage Text.Text)) effs
    )
    => RequestHandler effs ContractPABRequest ContractResponse
processNotificationEffects =
    maybeToHandler (extract Events.Contract._SendNotificationRequest)
    >>> RequestHandler.handleContractNotifications
    >>^ NotificationResponse


newtype MaxIterations = MaxIterations Int
    deriving stock (Eq, Ord, Show, Generic)
    deriving newtype (ToJSON, FromJSON)

defaultMaxIterations :: MaxIterations
defaultMaxIterations = MaxIterations 20

-- | Log messages about the
data ContractInstanceMsg t =
    ProcessFirstInboxMessage ContractInstanceId (Response ContractResponse)
    | SendingContractStateMessages ContractInstanceId IterationID [Request ContractPABRequest]
    | LookingUpStateOfContractInstance
    | CurrentIteration IterationID
    | InboxMessageDoesntMatchIteration IterationID IterationID
    | InboxMessageMatchesIteration
    | InvokingContractUpdate
    | ObtainedNewState
    | UpdatedContract ContractInstanceId IterationID
    | LookingUpContract (Contract.ContractDef t)
    | InitialisingContract (Contract.ContractDef t) ContractInstanceId
    | InitialContractResponse (Contract.State t)
    | ActivatedContractInstance (Contract.ContractDef t) ContractInstanceId
    | RunRequestHandler ContractInstanceId Int -- number of requests
    | RunRequestHandlerDidNotHandleAnyEvents
    | StoringSignedTx Tx
    | CallingEndpoint String ContractInstanceId JSON.Value
    | ProcessContractInbox ContractInstanceId
    | HandlingRequest RequestHandlerLogMsg
    | HandlingRequests ContractInstanceId [Request ContractPABRequest]
    | BalancingTx TxBalanceMsg
    | MaxIterationsExceeded ContractInstanceId MaxIterations
    | NotificationFailed NotificationError
    deriving stock (Generic)

deriving stock instance (Eq (Contract.State t), Eq (Contract.ContractDef t)) => Eq (ContractInstanceMsg t)
deriving anyclass instance (ToJSON (Contract.State t), ToJSON (Contract.ContractDef t)) => ToJSON (ContractInstanceMsg t)
deriving anyclass instance (FromJSON (Contract.State t), FromJSON (Contract.ContractDef t)) => FromJSON (ContractInstanceMsg t)

instance (ToJSON (Contract.State t), ToJSON (Contract.ContractDef t)) => ToObject (ContractInstanceMsg t) where
    toObject v = \case
        ProcessFirstInboxMessage instanceID response ->
            mkObjectStr "Processing first contract inbox message" $
                case v of
                    MaximalVerbosity -> Left (instanceID, Tagged @"response" response)
                    _                -> Right instanceID
        SendingContractStateMessages instanceID iterationID requests ->
            mkObjectStr "Sending contact state messages" $
                case v of
                    MaximalVerbosity ->
                        Left (instanceID, iterationID, Tagged @"requests" requests)
                    _ -> Right instanceID
        LookingUpStateOfContractInstance -> mkObjectStr "looking up state of contract instance" ()
        CurrentIteration i -> mkObjectStr "current iteration" i
        InboxMessageDoesntMatchIteration i1 i2 ->
            mkObjectStr
                "inbox message doesn't match iteration"
                (i1, Tagged @"inbox_message_iteration" i2)
        InboxMessageMatchesIteration -> mkObjectStr "inbox message matches iteration" ()
        InvokingContractUpdate -> mkObjectStr "invoking contract update" ()
        ObtainedNewState -> mkObjectStr "obtained new state" ()
        UpdatedContract instanceID iterationID ->
            mkObjectStr "updated contract" (instanceID, iterationID)
        LookingUpContract t ->
            mkObjectStr "looking up contract" (Tagged @"contract" t)
        InitialisingContract t instanceID ->
            mkObjectStr "initialising contract" (Tagged @"contract" t, instanceID)
        InitialContractResponse rsp ->
            mkObjectStr "initial contract response" $
                case v of
                    MaximalVerbosity -> Left (Tagged @"response" rsp)
                    _                -> Right ()
        ActivatedContractInstance _ instanceID ->
            mkObjectStr "activated contract instance" instanceID
        RunRequestHandler instanceID n ->
            mkObjectStr "running request handler" (instanceID, Tagged @"num_requests" n)
        RunRequestHandlerDidNotHandleAnyEvents ->
            mkObjectStr "request handler did not handle any events" ()
        StoringSignedTx t ->
            mkObjectStr "storing signed tx" $
                case v of
                    MaximalVerbosity -> Left t
                    _                -> Right ()
        CallingEndpoint ep instanceID vl ->
            mkObjectStr "calling endpoint" $
                case v of
                    MinimalVerbosity -> Left (instanceID, Tagged @"endpoint" ep)
                    _                -> Right (instanceID, Tagged @"endpoint" ep, Tagged @"value" vl)
        ProcessContractInbox instanceID ->
            mkObjectStr "processing contract inbox" instanceID
        HandlingRequest reqLog ->
            mkObjectStr "handling request" (Tagged @"request" reqLog)
        HandlingRequests instanceID requests ->
            mkObjectStr "handling requests" $
                let n = length requests in
                case v of
                    MaximalVerbosity -> Left (instanceID, Tagged @"requests" requests, Tagged @"num_requests" n)
                    _                -> Right (instanceID, Tagged @"num_requests" n)
        BalancingTx m ->
            mkObjectStr "balancing tx" $
                case v of
                    MaximalVerbosity -> Left m
                    _                -> Right ()
        MaxIterationsExceeded instanceID maxIts ->
            mkObjectStr "exceeded maximum number of iterations"
                (instanceID, Tagged @"max_iterations" maxIts)
        NotificationFailed _ ->
            mkObjectStr "notification failed" ()

instance (Pretty (Contract.State t), Pretty (Contract.ContractDef t)) => Pretty (ContractInstanceMsg t) where
    pretty = \case
        ProcessFirstInboxMessage instanceID response ->
            "processFirstInboxMessage for" <+> pretty instanceID <> ". The first message is:" <+> pretty response
        SendingContractStateMessages contract iterationID requests ->
            "Sending messages for contract" <+> pretty contract <+> "at iteration" <+> pretty iterationID <+> ". The contract has the following requests:" <+> pretty requests
        LookingUpStateOfContractInstance -> "Looking up current state of the contract instance."
        CurrentIteration i -> "CurrentIteration:" <+> pretty i
        InboxMessageDoesntMatchIteration imsg iinstance -> "The iteration of the first inbox message" <+> parens (pretty imsg) <+> "does not match the contract instance's iteration" <+> parens (pretty iinstance) <> "."
        InboxMessageMatchesIteration -> "The iteration of the first inbox message matches the contract instance's iteration."
        InvokingContractUpdate -> "Invoking contract update."
        ObtainedNewState -> "Obtained new state. Sending contract state messages."
        UpdatedContract instanceID iterationID -> "Updated contract" <+> pretty instanceID <+> "to new iteration" <+> pretty iterationID
        LookingUpContract c -> "Looking up contract" <+> pretty c
        InitialisingContract c instanceID -> "Initialising contract" <+> pretty c <+> "with ID" <+> pretty instanceID
        InitialContractResponse rsp -> "Initial contract response:" <+> pretty rsp
        ActivatedContractInstance _ instanceID -> "Activated instance" <+> pretty instanceID
        RunRequestHandler instanceID numRequests -> "Running request handler for" <+> pretty instanceID <+> "with" <+> pretty numRequests <+> "requests."
        RunRequestHandlerDidNotHandleAnyEvents -> "runRequestHandler: did not handle any requests"
        StoringSignedTx tx -> "Storing signed tx" <+> pretty (txId tx)
        CallingEndpoint endpoint instanceID value ->
            "Calling endpoint" <+> pretty endpoint <+> "on instance" <+> pretty instanceID <+> "with" <+> viaShow value
        ProcessContractInbox i -> "Processing contract inbox for" <+> pretty i
        HandlingRequest msg -> pretty msg
        HandlingRequests i rqs -> "Handling" <+> pretty (length rqs) <+> "requests for" <+> pretty i
        BalancingTx msg -> pretty msg
        MaxIterationsExceeded i (MaxIterations is) -> "Max iterations" <+> parens (pretty is) <+> "exceeded for" <+> pretty i
        NotificationFailed e -> "Notification failed:" <+> pretty e
