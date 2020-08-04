{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Plutus.SCB.Core.ContractInstance(
    ContractInstanceMsg(..)
    , lookupContractState
    , processFirstInboxMessage
    , processAllContractInboxes
    , processContractInbox
    , lookupContract
    , activateContract
    -- * Contract outboxes
    , MaxIterations(..)
    , defaultMaxIterations
    , processAllContractOutboxes
    , processOwnPubkeyRequests
    , processAwaitSlotRequests
    , processUtxoAtRequests
    , processWriteTxRequests
    -- * Calling an endpoint
    , callContractEndpoint
    ) where

import           Control.Arrow                                   ((>>>), (>>^))
import           Control.Lens
import           Control.Monad                                   (void, when)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error                       (Error, throwError)
import           Control.Monad.Freer.Extra.Log
import           Control.Monad.Freer.Log                         (LogMessage, LogObserve, mapLog, surroundInfo)
import qualified Data.Aeson                                      as JSON
import           Data.Foldable                                   (traverse_)
import qualified Data.Map                                        as Map
import           Data.Maybe                                      (mapMaybe)
import           Data.Semigroup                                  (Last (..))
import qualified Data.Set                                        as Set
import qualified Data.Text                                       as Text
import           Data.Text.Prettyprint.Doc                       (Pretty, parens, pretty, viaShow, (<+>))

import           Language.Plutus.Contract.Effects.AwaitSlot      (WaitingForSlot (..))
import           Language.Plutus.Contract.Effects.ExposeEndpoint (ActiveEndpoint (..), EndpointDescription (..),
                                                                  EndpointValue (..))
import           Language.Plutus.Contract.Effects.WriteTx        (WriteTxResponse (..))
import           Language.Plutus.Contract.Resumable              (IterationID, Request (..), Response (..))
import           Language.Plutus.Contract.Trace.RequestHandler   (MaxIterations (..), RequestHandler (..),
                                                                  RequestHandlerLogMsg, defaultMaxIterations, extract,
                                                                  maybeToHandler, tryHandler, wrapHandler)
import qualified Language.Plutus.Contract.Trace.RequestHandler   as RequestHandler

import           Ledger.Tx                                       (Tx, txId)
import           Wallet.Effects                                  (ChainIndexEffect, SigningProcessEffect, WalletEffect)
import           Wallet.Emulator.LogMessages                     (TxBalanceMsg)

import           Plutus.SCB.Command                              (saveBalancedTx, saveBalancedTxResult,
                                                                  saveContractState, sendContractEvent)
import           Plutus.SCB.Effects.Contract                     (ContractCommand (..), ContractEffect)
import qualified Plutus.SCB.Effects.Contract                     as Contract
import           Plutus.SCB.Effects.EventLog                     (EventLogEffect, runCommand, runGlobalQuery)
import           Plutus.SCB.Effects.UUID                         (UUIDEffect, uuidNextRandom)
import           Plutus.SCB.Events                               (ChainEvent (..))
import           Plutus.SCB.Events.Contract                      (ContractEvent (..), ContractInstanceId (..),
                                                                  ContractInstanceState (..), ContractResponse (..),
                                                                  ContractSCBRequest (..),
                                                                  PartiallyDecodedResponse (..),
                                                                  unContractHandlersResponse)
import qualified Plutus.SCB.Events.Contract                      as Events.Contract
import qualified Plutus.SCB.Query                                as Query
import           Plutus.SCB.Types                                (SCBError (..), Source (ContractEventSource, NodeEventSource, UserEventSource, WalletEventSource))
import           Plutus.SCB.Utils                                (tshow)

import qualified Plutus.SCB.Core.Projections                     as Projections

data ContractInstanceMsg t =
    ProcessFirstInboxMessage ContractInstanceId (Response ContractResponse)
    | SendingContractStateMessages ContractInstanceId IterationID [Request ContractSCBRequest]
    | LookingUpStateOfContractInstance
    | CurrentIteration IterationID
    | InboxMessageDoesntMatchIteration IterationID IterationID
    | InboxMessageMatchesIteration
    | InvokingContractUpdate
    | ObtainedNewState
    | UpdatedContract ContractInstanceId IterationID
    | LookingUpContract t
    | InitialisingContract t ContractInstanceId
    | InitialContractResponse (PartiallyDecodedResponse ContractSCBRequest)
    | ActivatedContractInstance ContractInstanceId
    | RunRequestHandler ContractInstanceId Int -- number of requests
    | RunRequestHandlerDidNotHandleAnyEvents
    | StoringSignedTx Tx
    | CallingEndpoint String ContractInstanceId JSON.Value
    | ProcessContractInbox ContractInstanceId
    | HandlingRequest RequestHandlerLogMsg
    | HandlingRequests ContractInstanceId [Request ContractSCBRequest]
    | BalancingTx TxBalanceMsg
    | MaxIterationsExceeded ContractInstanceId MaxIterations

-- TODO:
-- 1. per-instanceID messages
-- 2. per-iteration messages for
--      * RequestHandlerLogMsg
--      * TxBalanceMsg

instance Pretty t => Pretty (ContractInstanceMsg t) where
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
        ActivatedContractInstance instanceID -> "Activated instance" <+> pretty instanceID
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

sendContractStateMessages ::
    forall t effs.
        ( Member (EventLogEffect (ChainEvent t)) effs
        , Member (LogMsg (ContractInstanceMsg t)) effs
        )
    => ContractInstanceState t
    -> Eff effs ()
sendContractStateMessages is = do
    logInfo @(ContractInstanceMsg t) $ SendingContractStateMessages (csContract is) (csCurrentIteration is) (hooks (csCurrentState is))
    void
        $ runCommand (sendContractEvent @t) ContractEventSource
        $ ContractInstanceStateUpdateEvent is
    void $ runCommand (saveContractState @t) UserEventSource is

sendContractMessage ::
    forall t effs.
        ( Member (EventLogEffect (ChainEvent t)) effs
        )
    => ContractInstanceId
    -> Response ContractResponse
    -> Eff effs [ChainEvent t]
sendContractMessage instanceID =
    runCommand (sendContractEvent @t) ContractEventSource
    . ContractInboxMessage instanceID

-- | Get the current state of the contract instance
lookupContractState ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member (Error SCBError) effs
    )
    => ContractInstanceId
    -> Eff effs (ContractInstanceState t)
lookupContractState instanceID = do
    mp <- runGlobalQuery (Query.contractState @t)
    case Map.lookup instanceID mp of
        Nothing -> throwError $ OtherError $ "Contract instance not found " <> tshow instanceID
        Just s  -> pure s

-- | For a given contract instance, take the first message
--   from the inbox and update the contract with it.
processFirstInboxMessage ::
    forall t effs.
        ( Member (EventLogEffect (ChainEvent t)) effs
        , Member (ContractEffect t) effs
        , Member (Error SCBError) effs
        , Member (LogMsg (ContractInstanceMsg t)) effs
        , Member (LogObserve (LogMessage Text.Text)) effs
        )
    => ContractInstanceId
    -> Last (Response ContractResponse)
    -> Eff effs ()
processFirstInboxMessage instanceID (Last msg) = surroundInfo @Text.Text "processFirstInboxMessage" $ do
    logInfo @(ContractInstanceMsg t) $ ProcessFirstInboxMessage instanceID msg
    logInfo @(ContractInstanceMsg t) $ LookingUpStateOfContractInstance
    -- look up contract 't'
    ContractInstanceState{csCurrentIteration, csCurrentState, csContractDefinition} <- lookupContractState @t instanceID
    logInfo @(ContractInstanceMsg t) $ CurrentIteration csCurrentIteration
    if csCurrentIteration /= rspItID msg
        then logInfo @(ContractInstanceMsg t) $ InboxMessageDoesntMatchIteration (rspItID msg) csCurrentIteration
        else do
            logInfo @(ContractInstanceMsg t) InboxMessageMatchesIteration
            -- process the message
            let payload = Contract.contractMessageToPayload msg
            logInfo @(ContractInstanceMsg t) InvokingContractUpdate
            newState <- Contract.invokeContractUpdate_ csContractDefinition csCurrentState payload
            logInfo @(ContractInstanceMsg t) ObtainedNewState
            -- send out the new requests
            -- see note [Contract Iterations]
            let newIteration = succ csCurrentIteration
            sendContractStateMessages $ ContractInstanceState instanceID newIteration newState csContractDefinition
            logInfo @(ContractInstanceMsg t) $ UpdatedContract instanceID newIteration


-- | Check the inboxes of all contracts.
processAllContractInboxes ::
    forall t effs.
        ( Member (EventLogEffect (ChainEvent t)) effs
        , Member (ContractEffect t) effs
        , Member (Error SCBError) effs
        , Member (LogObserve (LogMessage Text.Text)) effs
        , Member (LogMsg (ContractInstanceMsg t)) effs
        )
    => Eff effs ()
processAllContractInboxes = surroundInfo @Text.Text "processAllContractInboxes" $ do
    state <- runGlobalQuery (Query.inboxMessages @t)
    itraverse_ (processFirstInboxMessage @t) state

-- | Check the inboxes of all contracts.
processContractInbox ::
    forall t effs.
        ( Member (EventLogEffect (ChainEvent t)) effs
        , Member (ContractEffect t) effs
        , Member (Error SCBError) effs
        , Member (LogObserve (LogMessage Text.Text)) effs
        , Member (LogMsg (ContractInstanceMsg t)) effs
        )
    => ContractInstanceId
    -> Eff effs ()
processContractInbox i = surroundInfo @Text.Text "processContractInbox" $ do
    logInfo @(ContractInstanceMsg t) $ ProcessContractInbox i
    state <- runGlobalQuery (Query.inboxMessages @t)
    traverse_ (processFirstInboxMessage @t i) (Map.lookup i state)

-- | Generic error message for failures during the contract lookup
newtype ContractLookupError = ContractLookupError { unContractLookupError :: String }

lookupContract ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Show t
    , Ord t
    )
    => t
    -> Eff effs (Either ContractLookupError t)
lookupContract t = do
    installed <- Projections.installedContracts
    let matchingContracts =
            Set.filter
                (\cp -> cp == t)
                installed
    pure
        $ maybe
            (Left (ContractLookupError (show t)))
            Right
            (Set.lookupMin matchingContracts)

-- | Create a new instance of the contract
activateContract ::
    forall t effs.
    ( Member (LogMsg (ContractInstanceMsg t)) effs
    , Member (EventLogEffect (ChainEvent t)) effs
    , Member (Error SCBError) effs
    , Member UUIDEffect effs
    , Member (ContractEffect t) effs
    , Show t
    , Ord t
    )
    => t
    -> Eff effs (ContractInstanceState t)
activateContract contract = do
    logInfo @(ContractInstanceMsg t) $ LookingUpContract contract
    contractDef <-
        either (throwError . ContractNotFound . unContractLookupError) pure =<<
        lookupContract @t contract
    activeContractInstanceId <- ContractInstanceId <$> uuidNextRandom
    logInfo $ InitialisingContract contract activeContractInstanceId
    let initialIteration = succ mempty -- FIXME get max it. from initial response
    response <- fmap (fmap unContractHandlersResponse) <$> Contract.invokeContract @t $ InitContract contractDef
    logInfo @(ContractInstanceMsg t) $ InitialContractResponse response
    let instanceState = ContractInstanceState
                          { csContract = activeContractInstanceId
                          , csCurrentIteration = initialIteration
                          , csCurrentState = response
                          , csContractDefinition = contract
                          }
    sendContractStateMessages instanceState
    logInfo @(ContractInstanceMsg t) $ ActivatedContractInstance activeContractInstanceId
    pure instanceState

respondtoRequests ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member (LogMsg (ContractInstanceMsg t)) effs
    , Member (ContractEffect t) effs
    , Member (Error SCBError) effs
    , Member (LogObserve (LogMessage Text.Text)) effs
    )
    => MaxIterations
    -> RequestHandler effs ContractSCBRequest ContractResponse
    -> Eff effs ()
respondtoRequests (MaxIterations mi) handler = do
    contractStates <- runGlobalQuery (Query.contractState @t)
    let state = fmap (hooks . csCurrentState) contractStates
    ifor_ state $ \instanceId requests ->
        let go j
             | j >= mi = do
                 logWarn @(ContractInstanceMsg t) $ MaxIterationsExceeded instanceId (MaxIterations mi)
             | otherwise = do
                 logDebug @(ContractInstanceMsg t) $ HandlingRequests instanceId requests
                 events <- runRequestHandler @t handler instanceId requests
                 when (not $ null events) (go $ succ j)
        in go 0

-- | Run a 'RequestHandler' on the 'ContractSCBRequest' list of a contract
--   instance and send the responses to the contract instance.
runRequestHandler ::
    forall t effs req.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member (LogMsg (ContractInstanceMsg t)) effs
    , Member (ContractEffect t) effs
    , Member (Error SCBError) effs
    , Member (LogObserve (LogMessage Text.Text)) effs
    )
    => RequestHandler effs req ContractResponse
    -> ContractInstanceId
    -> [Request req]
    -> Eff effs [ChainEvent t]
runRequestHandler h contractInstance requests = do
    logDebug @(ContractInstanceMsg t) $ RunRequestHandler contractInstance (length requests)
    -- try the handler on the requests until it succeeds for the first time,
    -- then stop. We want to handle at most 1 request per iteration.
    (response :: Maybe (Response ContractResponse)) <-
        tryHandler (wrapHandler h) requests

    case response of
        Just rsp -> do
            events <- sendContractMessage @t contractInstance rsp
            processContractInbox @t contractInstance
            pure events
        _ -> do
            logDebug @(ContractInstanceMsg t) RunRequestHandlerDidNotHandleAnyEvents
            pure []

processOwnPubkeyRequests ::
    forall effs.
    ( Member (LogObserve (LogMessage Text.Text)) effs
    , Member WalletEffect effs
    )
    => RequestHandler effs ContractSCBRequest ContractResponse
processOwnPubkeyRequests =
    maybeToHandler (extract Events.Contract._OwnPubkeyRequest) >>>
        fmap OwnPubkeyResponse RequestHandler.handleOwnPubKey

processAwaitSlotRequests ::
    forall effs.
    ( Member (LogObserve (LogMessage Text.Text)) effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    , Member WalletEffect effs
    )
    => RequestHandler effs ContractSCBRequest ContractResponse
processAwaitSlotRequests =
    maybeToHandler (fmap unWaitingForSlot . extract Events.Contract._AwaitSlotRequest)
    >>> RequestHandler.handleSlotNotifications
    >>^ AwaitSlotResponse

processUtxoAtRequests ::
    forall effs.
    ( Member ChainIndexEffect effs
    , Member (LogObserve (LogMessage Text.Text)) effs
    )
    => RequestHandler effs ContractSCBRequest ContractResponse
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
    , Member SigningProcessEffect effs
    )
    => RequestHandler effs ContractSCBRequest ContractResponse
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
    )
    => RequestHandler effs ContractSCBRequest ContractResponse
processNextTxAtRequests =
    maybeToHandler (extract Events.Contract._NextTxAtRequest)
    >>> RequestHandler.handleNextTxAtQueries
    >>^ NextTxAtResponse

processTxConfirmedRequests ::
    forall effs.
    ( Member ChainIndexEffect effs
    , Member (LogObserve (LogMessage Text.Text)) effs
    )
    => RequestHandler effs ContractSCBRequest ContractResponse
processTxConfirmedRequests =
    maybeToHandler (extract Events.Contract._AwaitTxConfirmedRequest)
    >>> RequestHandler.handleTxConfirmedQueries
    >>^ AwaitTxConfirmedResponse

callContractEndpoint ::
    forall t a effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member (ContractEffect t) effs
    , Member (LogMsg (ContractInstanceMsg t)) effs
    , Member (LogObserve (LogMessage Text.Text)) effs
    , Member (Error SCBError) effs
    , JSON.ToJSON a
    )
    => ContractInstanceId
    -> String
    -> a
    -> Eff effs [ChainEvent t]
callContractEndpoint inst endpointName endpointValue = do
    -- we can't use respondtoRequests here because we want to call the endpoint only on
    -- the contract instance 'inst'. And we want to error if the endpoint is not active.
    logInfo @(ContractInstanceMsg t) $ CallingEndpoint endpointName inst (JSON.toJSON endpointValue)
    state <- fmap (hooks . csCurrentState) <$> runGlobalQuery (Query.contractState @t)
    let activeEndpoints =
            filter ((==) (EndpointDescription endpointName) . aeDescription . rqRequest)
            $ mapMaybe (traverse (preview Events.Contract._UserEndpointRequest))
            $ Map.findWithDefault [] inst state

    when (null activeEndpoints) $
        throwError (OtherError $ "Contract " <> Text.pack (show inst) <> " has not requested endpoint " <> Text.pack endpointName)

    let handler _ = pure (UserEndpointResponse (EndpointDescription endpointName) (EndpointValue $ JSON.toJSON endpointValue))
    runRequestHandler (RequestHandler handler) inst activeEndpoints

-- | Look at the outboxes of all contract instances and process them.
processAllContractOutboxes ::
    forall t effs.
    ( Member (LogObserve (LogMessage Text.Text)) effs
    , Member (LogMsg (ContractInstanceMsg t)) effs
    , Member (EventLogEffect (ChainEvent t)) effs
    , Member WalletEffect effs
    , Member ChainIndexEffect effs
    , Member SigningProcessEffect effs
    , Member (Error SCBError) effs
    , Member (ContractEffect t) effs
    )
    => MaxIterations -- ^ Maximum number of times the requests for each contract instance are processed
    -> Eff effs ()
processAllContractOutboxes mi =
    mapLog @_ @(ContractInstanceMsg t) HandlingRequest
    $ mapLog @_ @(ContractInstanceMsg t) BalancingTx
    $ surroundInfo @Text.Text "processAllContractOutboxes"
    $ respondtoRequests @t @(LogMsg TxBalanceMsg ': LogMsg RequestHandlerLogMsg ': effs) mi
    $ contractRequestHandler @t @(LogMsg TxBalanceMsg ': LogMsg RequestHandlerLogMsg ': effs)

contractRequestHandler ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member ChainIndexEffect effs
    , Member WalletEffect effs
    , Member SigningProcessEffect effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    , Member (LogObserve (LogMessage Text.Text)) effs
    , Member (LogMsg (ContractInstanceMsg t)) effs
    , Member (LogMsg TxBalanceMsg) effs
    )
    => RequestHandler effs ContractSCBRequest ContractResponse
contractRequestHandler =
    processOwnPubkeyRequests @effs
    <> processAwaitSlotRequests @effs
    <> processUtxoAtRequests @effs
    <> processWriteTxRequests @t @effs
    <> processTxConfirmedRequests @effs
    <> processNextTxAtRequests @effs
