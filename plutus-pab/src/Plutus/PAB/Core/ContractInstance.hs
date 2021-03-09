{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
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
module Plutus.PAB.Core.ContractInstance(
    ContractInstanceMsg(..)
    , lookupContractState
    , processFirstInboxMessage
    , processAllContractInboxes
    , processContractInbox
    , lookupContract
    , activateContract
    , activateContractSTM
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
    , callContractEndpoint'
    -- * STM instances
    , startSTMInstanceThread
    , AppBackendConstraints
    ) where

import           Control.Arrow                                    ((>>>))
import           Control.Concurrent                               (forkIO)
import           Control.Concurrent.STM                           (STM)
import qualified Control.Concurrent.STM                           as STM
import           Control.Monad                                    (forM_, void)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error                        (Error, throwError)
import           Control.Monad.Freer.Extras.Log                   (LogMessage, LogMsg, LogObserve, logDebug, logInfo)
import           Control.Monad.Freer.Reader                       (Reader, ask, runReader)
import           Control.Monad.IO.Class                           (MonadIO (liftIO))
import           Data.List.NonEmpty                               (NonEmpty (..))
import qualified Data.List.NonEmpty                               as NEL
import qualified Data.Text                                        as Text

import           Plutus.Contract.Effects.AwaitSlot                (WaitingForSlot (..))
import           Plutus.Contract.Effects.ExposeEndpoint           (ActiveEndpoint (..))
import           Plutus.Contract.Resumable                        (Request (..), Response (..))
import           Plutus.Contract.Trace.RequestHandler             (RequestHandler (..), RequestHandlerLogMsg, extract,
                                                                   maybeToHandler, tryHandler', wrapHandler)
import           Plutus.PAB.Core.ContractInstance.RequestHandlers (ContractInstanceMsg (..), MaxIterations (..),
                                                                   defaultMaxIterations, processAwaitSlotRequests,
                                                                   processInstanceRequests, processNextTxAtRequests,
                                                                   processNotificationEffects, processOwnPubkeyRequests,
                                                                   processTxConfirmedRequests, processUtxoAtRequests,
                                                                   processWriteTxRequests)

import           Wallet.Effects                                   (ChainIndexEffect, ContractRuntimeEffect,
                                                                   WalletEffect)
import           Wallet.Emulator.LogMessages                      (TxBalanceMsg)

import           Plutus.Contract                         (AddressChangeRequest (..))
import           Plutus.PAB.Core.ContractInstance.STM             (Activity (Done), BlockchainEnv (..),
                                                                   InstanceState (..), InstancesState,
                                                                   emptyInstanceState)
import qualified Plutus.PAB.Core.ContractInstance.STM             as InstanceState
import           Plutus.PAB.Effects.Contract                      (ContractEffect, ContractStore)
import qualified Plutus.PAB.Effects.Contract                      as Contract
import           Plutus.PAB.Effects.EventLog                      (EventLogEffect)
import           Plutus.PAB.Effects.UUID                          (UUIDEffect, uuidNextRandom)
import           Plutus.PAB.Events                                (ChainEvent (..))
import           Plutus.PAB.Events.Contract                       (ContractInstanceId (..), ContractInstanceState (..),
                                                                   ContractPABRequest (..), ContractResponse (..),
                                                                   PartiallyDecodedResponse (..),
                                                                   unContractHandlersResponse)
import qualified Plutus.PAB.Events.Contract                       as Events.Contract
import           Plutus.PAB.Types                                 (PABError (..))

-- | Create a new instance of the contract
activateContractSTM ::
    forall t m appBackend effs.
    ( Member (LogMsg (ContractInstanceMsg t)) effs
    , Member (Error PABError) effs
    , Member UUIDEffect effs
    , Member (ContractEffect t) effs
    , Member (ContractStore t) effs
    , Member (Reader InstancesState) effs
    , Show t
    , Ord t
    , AppBackendConstraints t m appBackend
    , LastMember m (Reader ContractInstanceId ': appBackend)
    , LastMember m effs
    )
    => (Eff appBackend ~> IO)
    -> ContractDef t
    -> Eff effs ContractInstanceId
activateContractSTM runAppBackend contract = do
    activeContractInstanceId <- ContractInstanceId <$> uuidNextRandom
    logDebug $ InitialisingContract contract activeContractInstanceId
    initialState <- Contract.initialState contract
    Contract.putState contract activeContractInstanceId initialState
    s <- startSTMInstanceThread @t @m runAppBackend activeContractInstanceId
    ask >>= void . liftIO . STM.atomically . InstanceState.insertInstance activeContractInstanceId s
    logInfo @(ContractInstanceMsg t) $ ActivatedContractInstance initialState activeContractInstanceId
    pure activeContractInstanceId

processAwaitSlotRequestsSTM ::
    forall effs.
    ( Member (Reader BlockchainEnv) effs
    )
    => RequestHandler effs ContractPABRequest (STM ContractResponse)
processAwaitSlotRequestsSTM =
    maybeToHandler (fmap unWaitingForSlot . extract Events.Contract._AwaitSlotRequest)
    >>> (RequestHandler $ \targetSlot -> fmap AwaitSlotResponse . InstanceState.awaitSlot targetSlot <$> ask)

processTxConfirmedRequestsSTM ::
    forall effs.
    ( Member (Reader BlockchainEnv) effs
    )
    => RequestHandler effs ContractPABRequest (STM ContractResponse)
processTxConfirmedRequestsSTM =
    maybeToHandler (extract Events.Contract._NextTxAtRequest)
    >>> RequestHandler handler
    where
        handler req = do
            env <- ask
            pure (NextTxAtResponse <$> InstanceState.waitForAddressChange req env)

processEndpointRequestsSTM ::
    forall effs.
    ( Member (Reader InstanceState) effs
    )
    => RequestHandler effs (Request ContractPABRequest) (Response (STM ContractResponse))
processEndpointRequestsSTM =
    maybeToHandler (traverse (extract Events.Contract._UserEndpointRequest))
    >>> (RequestHandler $ \q@Request{rqID, itID, rqRequest} -> fmap (Response rqID itID) (fmap (UserEndpointResponse (aeDescription rqRequest)) . InstanceState.awaitEndpointResponse q <$> ask))

-- | 'RequestHandler' that uses TVars to wait for events
stmRequestHandler ::
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
    , Member (Reader BlockchainEnv) effs
    , Member (Reader InstanceState) effs
    )
    => RequestHandler effs (Request ContractPABRequest) (STM (Response ContractResponse))
stmRequestHandler = fmap sequence (wrapHandler (fmap pure nonBlockingRequests) <> blockingRequests) where

    -- requests that can be handled by 'WalletEffect', 'ChainIndexEffect', etc.
    nonBlockingRequests =
        processOwnPubkeyRequests @effs
        <> processUtxoAtRequests @effs
        <> processWriteTxRequests @t @effs
        <> processTxConfirmedRequests @effs
        <> processNextTxAtRequests @effs
        <> processInstanceRequests @effs
        <> processNotificationEffects @effs

    -- requests that wait for changes to happen
    blockingRequests =
        wrapHandler (processAwaitSlotRequestsSTM @effs)
        <> wrapHandler (processTxConfirmedRequestsSTM @effs)
        <> processEndpointRequestsSTM @effs

-- | Start the thread for the contract instance
startSTMInstanceThread ::
    forall t m appBackend effs.
    ( LastMember m effs
    , AppBackendConstraints t m appBackend
    , LastMember m (Reader InstanceState ': Reader ContractInstanceId ': appBackend)
    )
    => (Eff appBackend ~> IO)
    -> ContractInstanceId
    -> Eff effs InstanceState
startSTMInstanceThread runAppBackend instanceID = do
    state <- liftIO $ STM.atomically emptyInstanceState
    _ <- liftIO
        $ forkIO
        $ runAppBackend
        $ runReader instanceID
        $ runReader state
        $ stmInstanceLoop @t @m @(Reader InstanceState ': Reader ContractInstanceId ': appBackend) instanceID

    pure state
    -- TODO: Separate chain index queries (non-blocking) from waiting for updates (blocking)

type AppBackendConstraints t m effs =
    ( LastMember m effs
    , MonadIO m
    , Member (EventLogEffect (ChainEvent t)) effs
    , Member (Error PABError) effs
    , Member (LogMsg (ContractInstanceMsg t)) effs
    , Member ChainIndexEffect effs
    , Member WalletEffect effs
    , Member ContractRuntimeEffect effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    , Member (LogObserve (LogMessage Text.Text)) effs
    , Member (LogMsg TxBalanceMsg) effs
    , Member (ContractEffect t) effs
    , Member (Reader BlockchainEnv) effs
    )

-- | Handle requests using 'respondToRequestsSTM' until the contract is done.
stmInstanceLoop ::
    forall t m effs.
    ( AppBackendConstraints t m effs
    , Member (Reader InstanceState) effs
    , Member (Reader ContractInstanceId) effs
    )
    => ContractInstanceId
    -> Eff effs ()
stmInstanceLoop instanceId = do
    requests <- hooks . csCurrentState <$> lookupContractState @t instanceId
    updateState requests
    case requests of
        [] -> do
            ask >>= liftIO . STM.atomically . InstanceState.setActivity Done
        (x:xs) -> do
            response <- respondToRequestsSTM @t instanceId (x :| xs)
            event <- liftIO $ STM.atomically response
            _ <- sendContractMessage @t instanceId event
            processContractInbox @t instanceId
            stmInstanceLoop @t instanceId

-- | Update the TVars in the 'InstanceState' with data from the list
--   of requests.
updateState ::
    forall m effs.
    ( LastMember m effs
    , MonadIO m
    , Member (Reader InstanceState) effs
    )
    => [Request ContractPABRequest]
    -> Eff effs ()
updateState requests = do
    state <- ask
    liftIO $ putStrLn "ContractInstance: updateState"
    liftIO $ STM.atomically $ do
        InstanceState.clearEndpoints state
        forM_ requests $ \r -> do
            case rqRequest r of
                AwaitTxConfirmedRequest txid -> InstanceState.addTransaction txid state
                UtxoAtRequest addr -> InstanceState.addAddress addr state
                NextTxAtRequest AddressChangeRequest{acreqAddress} -> InstanceState.addAddress acreqAddress state
                UserEndpointRequest endpoint -> InstanceState.addEndpoint (r { rqRequest = endpoint}) state
                _ -> pure ()

-- | Run the STM-based request handler on a non-empty list
--   of requests.
respondToRequestsSTM ::
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
    , Member (Reader BlockchainEnv) effs
    , Member (Reader InstanceState) effs
    )
    => ContractInstanceId
    -> NonEmpty (Request ContractPABRequest)
    -> Eff effs (STM (Response ContractResponse))
respondToRequestsSTM instanceId requests = do
    logDebug @(ContractInstanceMsg t) $ HandlingRequests instanceId (NEL.toList requests)
    tryHandler' (stmRequestHandler @t) (NEL.toList requests)
