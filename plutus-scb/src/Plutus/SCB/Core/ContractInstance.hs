{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Plutus.SCB.Core.ContractInstance(
    lookupContractState
    , processFirstInboxMessage
    , processAllContractInboxes
    , processContractInbox
    , lookupContract
    , activateContract
    -- * Contract outboxes
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
import qualified Data.Aeson                                      as JSON
import           Data.Foldable                                   (traverse_)
import qualified Data.Map                                        as Map
import           Data.Maybe                                      (mapMaybe)
import           Data.Semigroup                                  (Last (..))
import qualified Data.Set                                        as Set
import qualified Data.Text                                       as Text
import           Data.Text.Prettyprint.Doc                       (Pretty, pretty, (<+>))

import           Language.Plutus.Contract.Effects.AwaitSlot      (WaitingForSlot (..))
import           Language.Plutus.Contract.Effects.ExposeEndpoint (ActiveEndpoint (..), EndpointDescription (..),
                                                                  EndpointValue (..))
import           Language.Plutus.Contract.Effects.WriteTx        (WriteTxResponse (..))
import           Language.Plutus.Contract.Resumable              (Request (..), Response (..))
import           Language.Plutus.Contract.Trace.RequestHandler   (RequestHandler (..), extract, maybeToHandler,
                                                                  tryHandler, wrapHandler)
import qualified Language.Plutus.Contract.Trace.RequestHandler   as RequestHandler

import           Wallet.Effects                                  (ChainIndexEffect, SigningProcessEffect, WalletEffect)

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
import           Plutus.SCB.Utils                                (render, tshow)

import qualified Plutus.SCB.Core.Projections                     as Projections

sendContractStateMessages ::
    forall t effs.
        ( Member (EventLogEffect (ChainEvent t)) effs
        , Member Log effs
        )
    => ContractInstanceState t
    -> Eff effs ()
sendContractStateMessages is = do
    logInfo . render $ "Sending messages for contract" <+> pretty (csContract is) <+> "at iteration" <+> pretty (csCurrentIteration is)
    logInfo . render $ "The contract has the following requests:" <+> pretty (fmap (\rq -> rq{rqRequest = ()}) $ hooks (csCurrentState is))
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
        , Member Log effs
        )
    => ContractInstanceId
    -> Last (Response ContractResponse)
    -> Eff effs ()
processFirstInboxMessage instanceID (Last msg) = do
    logInfo $ "processFirstInboxMessage start for " <> render (pretty instanceID)
    logInfo . render $ "The first message is: " <+> pretty msg
    logInfo "Looking up current state of the contract instance."
    -- look up contract 't'
    ContractInstanceState{csCurrentIteration, csCurrentState, csContractDefinition} <- lookupContractState @t instanceID
    logInfo . render $ "Current iteration:" <+> pretty csCurrentIteration
    if csCurrentIteration /= rspItID msg
        then logInfo "The first inbox message does not match the contract instance's iteration."
        else do
            logInfo "The first inbox message matches the contract instance's iteration."
            -- process the message
            let payload = Contract.contractMessageToPayload msg
            logInfo "Invoking contract update."
            newState <- Contract.invokeContractUpdate_ csContractDefinition csCurrentState payload
            logInfo "Obtained new state. Sending contract state messages."
            -- send out the new requests
            -- see note [Contract Iterations]
            let newIteration = succ csCurrentIteration
            sendContractStateMessages $ ContractInstanceState instanceID newIteration newState csContractDefinition
            logInfo . render $ "Updated contract" <+> pretty instanceID <+> "to new iteration" <+> pretty newIteration
    logInfo "processFirstInboxMessage end"

-- | Check the inboxes of all contracts.
processAllContractInboxes ::
    forall t effs.
        ( Member (EventLogEffect (ChainEvent t)) effs
        , Member (ContractEffect t) effs
        , Member (Error SCBError) effs
        , Member Log effs
        )
    => Eff effs ()
processAllContractInboxes = do
    logInfo "processAllContractInboxes start"
    state <- runGlobalQuery (Query.inboxMessages @t)
    itraverse_ (processFirstInboxMessage @t) state
    logInfo "processAllContractInboxes end"

-- | Check the inboxes of all contracts.
processContractInbox ::
    forall t effs.
        ( Member (EventLogEffect (ChainEvent t)) effs
        , Member (ContractEffect t) effs
        , Member (Error SCBError) effs
        , Member Log effs
        )
    => ContractInstanceId
    -> Eff effs ()
processContractInbox i = do
    logInfo "processContractInbox start"
    logInfo $ render $ pretty i
    state <- runGlobalQuery (Query.inboxMessages @t)
    traverse_ (processFirstInboxMessage @t i) (Map.lookup i state)
    logInfo "processContractInbox end"

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
    ( Member Log effs
    , Member (EventLogEffect (ChainEvent t)) effs
    , Member (Error SCBError) effs
    , Member UUIDEffect effs
    , Member (ContractEffect t) effs
    , Show t
    , Pretty t
    , Ord t
    )
    => t
    -> Eff effs (ContractInstanceState t)
activateContract contract = do
    logInfo . render $ "Finding contract" <+> pretty contract
    contractDef <-
        either (throwError . ContractNotFound . unContractLookupError) pure =<<
        lookupContract @t contract
    activeContractInstanceId <- ContractInstanceId <$> uuidNextRandom
    logInfo . render $ "Initializing contract instance with ID" <+> pretty activeContractInstanceId
    let initialIteration = succ mempty -- FIXME get max it. from initial response
    response <- fmap (fmap unContractHandlersResponse) <$> Contract.invokeContract @t $ InitContract contractDef
    logInfo . render $ "Response was: " <+> pretty response
    let instanceState = ContractInstanceState
                          { csContract = activeContractInstanceId
                          , csCurrentIteration = initialIteration
                          , csCurrentState = response
                          , csContractDefinition = contract
                          }
    sendContractStateMessages instanceState
    logInfo . render $ "Activated contract instance:" <+> pretty activeContractInstanceId
    pure instanceState

respondtoRequests ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member Log effs
    , Member (ContractEffect t) effs
    , Member (Error SCBError) effs
    )
    => RequestHandler effs ContractSCBRequest ContractResponse
    -> Eff effs ()
respondtoRequests handler = do
    contractStates <- runGlobalQuery (Query.contractState @t)
    let state = fmap (hooks . csCurrentState) contractStates
    itraverse_ (runRequestHandler @t handler) state

-- | Run a 'RequestHandler' on the 'ContractSCBRequest' list of a contract
--   instance and send the responses to the contract instance.
runRequestHandler ::
    forall t effs req.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member Log effs
    , Member (ContractEffect t) effs
    , Member (Error SCBError) effs
    )
    => RequestHandler effs req ContractResponse
    -> ContractInstanceId
    -> [Request req]
    -> Eff effs [ChainEvent t]
runRequestHandler h contractInstance requests = do
    logDebug . render $ "runRequestHandler for" <+> pretty contractInstance <+> "with" <+> pretty (length requests) <+> "requests"
    logDebug . render . pretty . fmap (\req -> req{rqRequest = ()}) $ requests

    -- try the handler on the requests until it succeeds for the first time, then stop.
    -- We want to handle at most 1 request per iteration.
    (response :: Maybe (Response ContractResponse)) <-
        tryHandler (wrapHandler h) requests

    case response of
        Just rsp -> do
            events <- sendContractMessage @t contractInstance rsp
            processContractInbox @t contractInstance
            pure events
        _ -> do
            logDebug "runRequestHandler: did not handle any requests"
            pure []

processOwnPubkeyRequests ::
    forall effs.
    ( Member Log effs
    , Member WalletEffect effs
    )
    => RequestHandler effs ContractSCBRequest ContractResponse
processOwnPubkeyRequests =
    maybeToHandler (extract Events.Contract._OwnPubkeyRequest) >>>
        fmap OwnPubkeyResponse RequestHandler.handleOwnPubKey

processAwaitSlotRequests ::
    forall effs.
    ( Member Log effs
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
    , Member Log effs
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
    , Member Log effs
    , Member SigningProcessEffect effs
    )
    => RequestHandler effs ContractSCBRequest ContractResponse
processWriteTxRequests =
    let store result = case result of
            Left err -> pure (Left err)
            Right signedTx -> do
                logInfo $ "Storing signed TX: " <> tshow signedTx
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
    ( Member Log effs
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
    , Member Log effs
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
    , Member Log effs
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
    logInfo . render $ "calling endpoint" <+> pretty endpointName <+> "on instance" <+> pretty inst
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
    ( Member Log effs
    , Member (EventLogEffect (ChainEvent t)) effs
    , Member WalletEffect effs
    , Member ChainIndexEffect effs
    , Member SigningProcessEffect effs
    , Member (Error SCBError) effs
    , Member (ContractEffect t) effs
    )
    => Eff effs ()
processAllContractOutboxes = do
    logInfo "processAllContractOutboxes start"
    respondtoRequests @t @effs (contractRequestHandler @t @effs)
    logInfo "processAllContractOutboxes end"

contractRequestHandler ::
    forall t effs.
    ( Member (EventLogEffect (ChainEvent t)) effs
    , Member ChainIndexEffect effs
    , Member WalletEffect effs
    , Member SigningProcessEffect effs
    , Member Log effs
    )
    => RequestHandler effs ContractSCBRequest ContractResponse
contractRequestHandler =
    processOwnPubkeyRequests @effs
    <> processAwaitSlotRequests @effs
    <> processUtxoAtRequests @effs
    <> processWriteTxRequests @t @effs
    <> processTxConfirmedRequests @effs
    <> processNextTxAtRequests @effs
