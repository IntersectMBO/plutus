{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
-- | The polling-based contract instance runner.
module Plutus.PAB.Core.ContractInstance.Polling(
    processAllContractOutboxes
    , callContractEndpoint
    , callContractEndpoint'
    , processFirstInboxMessage
    , sendContractStateMessages
    , lookupContractState
    , sendContractMessage
    , processContractInbox
    , processAllContractInboxes
    , lookupContract
    , ContractLookupError(..)
    , activateContract
    ) where

import           Control.Lens
import           Control.Monad                                    (unless, void, when)
import           Control.Monad.Freer                              (Eff, Member, interpret)
import           Control.Monad.Freer.Error                        (Error, throwError)
import           Control.Monad.Freer.Extras.Log                   (LogMessage, LogMsg, LogObserve, logDebug, logInfo,
                                                                   logWarn, mapLog, surroundInfo)
import           Control.Monad.Freer.Extras.Modify                (wrapError)
import           Control.Monad.Freer.Reader                       (Reader, runReader)
import qualified Data.Aeson                                       as JSON
import           Data.Foldable                                    (for_, traverse_)
import qualified Data.Map                                         as Map
import           Data.Maybe                                       (mapMaybe)
import           Data.Semigroup                                   (Last (..))
import qualified Data.Set                                         as Set
import qualified Data.Text                                        as Text
import           Data.Text.Extras                                 (tshow)
import           Plutus.Contract.Effects.ExposeEndpoint           (ActiveEndpoint (..), EndpointDescription (..),
                                                                   EndpointValue (..))
import           Plutus.Contract.Resumable                        (Request (..), Response (..))
import           Plutus.Contract.Trace                            (EndpointError (..))
import           Plutus.Contract.Trace.RequestHandler             (RequestHandler (..), RequestHandlerLogMsg,
                                                                   tryHandler, wrapHandler)
import           Plutus.PAB.Command                               (sendContractEvent)
import           Plutus.PAB.Core.ContractInstance.RequestHandlers (ContractInstanceMsg (..), MaxIterations (..),
                                                                   processAwaitSlotRequests, processInstanceRequests,
                                                                   processNextTxAtRequests, processNotificationEffects,
                                                                   processOwnPubkeyRequests, processTxConfirmedRequests,
                                                                   processUtxoAtRequests, processWriteTxRequests)
import qualified Plutus.PAB.Core.Projections                      as Projections
import           Plutus.PAB.Effects.Contract                      (ContractCommand (InitContract), ContractEffect)
import qualified Plutus.PAB.Effects.Contract                      as Contract
import           Plutus.PAB.Effects.EventLog                      (EventLogEffect, runCommand, runGlobalQuery)
import           Plutus.PAB.Effects.UUID                          (UUIDEffect, uuidNextRandom)
import           Plutus.PAB.Events                                (ChainEvent (..))
import           Plutus.PAB.Events.Contract                       (ContractEvent (..), ContractInstanceId (..),
                                                                   ContractInstanceState (..), ContractPABRequest (..),
                                                                   ContractResponse (..), PartiallyDecodedResponse (..),
                                                                   unContractHandlersResponse)
import qualified Plutus.PAB.Events.Contract                       as Events.Contract
import qualified Plutus.PAB.Query                                 as Query
import           Plutus.PAB.Types                                 (PABError (..), Source (..))
import           Wallet.Effects                                   (ChainIndexEffect, ContractRuntimeEffect,
                                                                   WalletEffect)
import           Wallet.Emulator.LogMessages                      (TxBalanceMsg)

-- | Call a named endpoint on a contract instance, throwing an 'PABError'
--   if the endpoint is not active.
callContractEndpoint ::
    forall t a effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member (LogMsg (ContractInstanceMsg t)) effs
    , Member (Error PABError) effs
    , JSON.ToJSON a
    )
    => ContractInstanceId
    -> String
    -> a
    -> Eff effs [ChainEvent t]
callContractEndpoint instanceID endpointName =
    wrapError (EndpointCallError instanceID) . callContractEndpoint' @t @a @(Error EndpointError ': effs) instanceID endpointName

-- | Call a named endpoint on a contract instance, throwing an 'EndpointError'
--   if the endpoint is not active.
callContractEndpoint' ::
    forall t a effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member (LogMsg (ContractInstanceMsg t)) effs
    , Member (Error EndpointError) effs
    , JSON.ToJSON a
    )
    => ContractInstanceId
    -> String
    -> a
    -> Eff effs [ChainEvent t]
callContractEndpoint' instanceID endpointName endpointValue = do
    -- we can't use respondtoRequests here because we want to call the endpoint only on
    -- the contract instance 'inst'. And we want to error if the endpoint is not active.
    logInfo @(ContractInstanceMsg t) $ CallingEndpoint endpointName instanceID (JSON.toJSON endpointValue)
    state <- fmap (hooks . csCurrentState) <$> runGlobalQuery (Query.contractState @t)
    let activeEndpoints =
            filter ((==) (EndpointDescription endpointName) . aeDescription . rqRequest)
            $ mapMaybe (traverse (preview Events.Contract._UserEndpointRequest))
            $ Map.findWithDefault [] instanceID state

    when (null activeEndpoints) $
        throwError $ EndpointNotActive Nothing (EndpointDescription endpointName)

    let handler _ = pure (UserEndpointResponse (EndpointDescription endpointName) (EndpointValue $ JSON.toJSON endpointValue))
    runRequestHandler (RequestHandler handler) instanceID activeEndpoints

-- | Look at the outboxes of all contract instances and process them.
processAllContractOutboxes ::
    forall t effs.
    ( Member (LogObserve (LogMessage Text.Text)) effs
    , Member (LogMsg (ContractInstanceMsg t)) effs
    , Member (EventLogEffect (ChainEvent t)) effs
    , Member WalletEffect effs
    , Member ChainIndexEffect effs
    , Member ContractRuntimeEffect effs
    , Member (Error PABError) effs
    , Member (ContractEffect t) effs
    )
    => MaxIterations -- ^ Maximum number of times the requests for each contract instance are processed
    -> Eff effs ()
processAllContractOutboxes mi =
    interpret (mapLog @_ @(ContractInstanceMsg t) HandlingRequest)
    $ interpret (mapLog @_ @(ContractInstanceMsg t) BalancingTx)
    $ surroundInfo @Text.Text "processAllContractOutboxes"
    $ respondtoRequests @t @(LogMsg TxBalanceMsg ': LogMsg RequestHandlerLogMsg ': effs) mi
    $ contractRequestHandler @t @(Reader ContractInstanceId ': LogMsg TxBalanceMsg ': LogMsg RequestHandlerLogMsg ': effs)

contractRequestHandler ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member ChainIndexEffect effs
    , Member WalletEffect effs
    , Member ContractRuntimeEffect effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    , Member (LogObserve (LogMessage Text.Text)) effs
    , Member (LogMsg (ContractInstanceMsg t)) effs
    , Member (LogMsg TxBalanceMsg) effs
    , Member (Reader ContractInstanceId) effs
    )
    => RequestHandler effs ContractPABRequest ContractResponse
contractRequestHandler =
    processOwnPubkeyRequests @effs
    <> processAwaitSlotRequests @effs
    <> processUtxoAtRequests @effs
    <> processWriteTxRequests @t @effs
    <> processTxConfirmedRequests @effs
    <> processNextTxAtRequests @effs
    <> processInstanceRequests @effs
    <> processNotificationEffects @effs

respondtoRequests ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member (LogMsg (ContractInstanceMsg t)) effs
    , Member (ContractEffect t) effs
    , Member (Error PABError) effs
    , Member (LogObserve (LogMessage Text.Text)) effs
    )
    => MaxIterations
    -> RequestHandler (Reader ContractInstanceId ': effs) ContractPABRequest ContractResponse
    -> Eff effs ()
respondtoRequests (MaxIterations mi) handler = do
    contractStates <- runGlobalQuery (Query.contractState @t)
    let instances = Map.keys contractStates
    for_ instances $ \instanceId ->
        let go j
             | j >= mi =
                 logWarn @(ContractInstanceMsg t) $ MaxIterationsExceeded instanceId (MaxIterations mi)
             | otherwise = do
                 requests <- hooks . csCurrentState <$> lookupContractState @t instanceId
                 logDebug @(ContractInstanceMsg t) $ HandlingRequests instanceId requests
                 events <- runReader instanceId $ runRequestHandler @t handler instanceId requests
                 processContractInbox @t instanceId
                 unless (null events) (go $ succ j)
        in go 0

-- | Run a 'RequestHandler' on the 'ContractPABRequest' list of a contract
--   instance and send the responses to the contract instance.
runRequestHandler ::
    forall t effs req.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member (LogMsg (ContractInstanceMsg t)) effs
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
        Just rsp ->
            sendContractMessage @t contractInstance rsp
        _ -> do
            logDebug @(ContractInstanceMsg t) RunRequestHandlerDidNotHandleAnyEvents
            pure []

-- | Get the current state of the contract instance
lookupContractState ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member (Error PABError) effs
    )
    => ContractInstanceId
    -> Eff effs (ContractInstanceState t)
lookupContractState instanceID = do
    mp <- runGlobalQuery (Query.contractState @t)
    case Map.lookup instanceID mp of
        Nothing -> throwError $ OtherError $ "Contract instance not found " <> tshow instanceID
        Just s  -> pure s

-- | Check the inboxes of a contract.
processContractInbox ::
    forall t effs.
        ( Member (EventLogEffect (ChainEvent t)) effs
        , Member (ContractEffect t) effs
        , Member (Error PABError) effs
        , Member (LogObserve (LogMessage Text.Text)) effs
        , Member (LogMsg (ContractInstanceMsg t)) effs
        )
    => ContractInstanceId
    -> Eff effs ()
processContractInbox i = surroundInfo @Text.Text "processContractInbox" $ do
    logDebug @(ContractInstanceMsg t) $ ProcessContractInbox i
    state <- runGlobalQuery (Query.inboxMessages @t)
    traverse_ (processFirstInboxMessage @t i) (Map.lookup i state)

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

-- | For a given contract instance, take the first message
--   from the inbox and update the contract with it.
processFirstInboxMessage ::
    forall t effs.
        ( Member (EventLogEffect (ChainEvent t)) effs
        , Member (ContractEffect t) effs
        , Member (Error PABError) effs
        , Member (LogMsg (ContractInstanceMsg t)) effs
        , Member (LogObserve (LogMessage Text.Text)) effs
        )
    => ContractInstanceId
    -> Last (Response ContractResponse)
    -> Eff effs ()
processFirstInboxMessage instanceID (Last msg) = surroundInfo @Text.Text "processFirstInboxMessage" $ do
    logInfo @(ContractInstanceMsg t) $ ProcessFirstInboxMessage instanceID msg
    logDebug @(ContractInstanceMsg t) $ LookingUpStateOfContractInstance
    -- look up contract 't'
    ContractInstanceState{csCurrentIteration, csCurrentState, csContractDefinition} <- lookupContractState @t instanceID
    logInfo @(ContractInstanceMsg t) $ CurrentIteration csCurrentIteration
    if csCurrentIteration /= rspItID msg
        then logDebug @(ContractInstanceMsg t) $ InboxMessageDoesntMatchIteration (rspItID msg) csCurrentIteration
        else do
            logDebug @(ContractInstanceMsg t) InboxMessageMatchesIteration
            -- process the message
            let payload = Contract.contractMessageToPayload msg
            logDebug @(ContractInstanceMsg t) InvokingContractUpdate
            newState <- Contract.invokeContractUpdate_ csContractDefinition csCurrentState payload
            logDebug @(ContractInstanceMsg t) ObtainedNewState
            -- send out the new requests
            -- see note [Contract Iterations]
            let newIteration = succ csCurrentIteration
            sendContractStateMessages $ ContractInstanceState instanceID newIteration newState csContractDefinition
            logDebug @(ContractInstanceMsg t) $ UpdatedContract instanceID newIteration

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

-- | Check the inboxes of all contracts.
processAllContractInboxes ::
    forall t effs.
        ( Member (EventLogEffect (ChainEvent t)) effs
        , Member (ContractEffect t) effs
        , Member (Error PABError) effs
        , Member (LogObserve (LogMessage Text.Text)) effs
        , Member (LogMsg (ContractInstanceMsg t)) effs
        )
    => Eff effs ()
processAllContractInboxes = surroundInfo @Text.Text "processAllContractInboxes" $ do
    state <- runGlobalQuery (Query.inboxMessages @t)
    itraverse_ (processFirstInboxMessage @t) state

-- | Create a new instance of the contract
activateContract ::
    forall t effs.
    ( Member (LogMsg (ContractInstanceMsg t)) effs
    , Member (EventLogEffect (ChainEvent t)) effs
    , Member (Error PABError) effs
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
