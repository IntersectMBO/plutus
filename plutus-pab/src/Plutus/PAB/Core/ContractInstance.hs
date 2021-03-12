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
{-

Start the threads for contract instances

-}
module Plutus.PAB.Core.ContractInstance(
    ContractInstanceMsg(..)
    , activateContractSTM
    , processWriteTxRequests
    -- * STM instances
    , startSTMInstanceThread
    , AppBackendConstraints
    -- * Calling endpoints
    , callEndpointOnInstance
    ) where

import           Control.Arrow                                    ((>>>))
import           Control.Concurrent                               (forkIO)
import           Control.Concurrent.STM                           (STM)
import qualified Control.Concurrent.STM                           as STM
import           Control.Monad                                    (forM_, void)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error                        (Error)
import           Control.Monad.Freer.Extras.Log                   (LogMessage, LogMsg, LogObserve, logDebug, logInfo)
import           Control.Monad.Freer.Reader                       (Reader, ask, runReader)
import           Control.Monad.IO.Class                           (MonadIO (liftIO))
import           Data.Proxy                                       (Proxy (..))
import qualified Data.Text                                        as Text

import           Plutus.Contract.Effects.AwaitSlot                (WaitingForSlot (..))
import           Plutus.Contract.Effects.ExposeEndpoint           (ActiveEndpoint (..))
import           Plutus.Contract.Resumable                        (Request (..), Response (..))
import           Plutus.Contract.Trace.RequestHandler             (RequestHandler (..), RequestHandlerLogMsg, extract,
                                                                   maybeToHandler, tryHandler', wrapHandler)
import           Plutus.PAB.Core.ContractInstance.RequestHandlers (ContractInstanceMsg (..), processInstanceRequests,
                                                                   processNextTxAtRequests, processNotificationEffects,
                                                                   processOwnPubkeyRequests, processTxConfirmedRequests,
                                                                   processUtxoAtRequests, processWriteTxRequests)

import           Wallet.Effects                                   (ChainIndexEffect, ContractRuntimeEffect,
                                                                   WalletEffect)
import           Wallet.Emulator.LogMessages                      (TxBalanceMsg)

import           Plutus.Contract                                  (AddressChangeRequest (..))
import           Plutus.PAB.Core.ContractInstance.STM             (Activity (Done), BlockchainEnv (..),
                                                                   InstanceState (..), InstancesState,
                                                                   callEndpointOnInstance, emptyInstanceState)
import qualified Plutus.PAB.Core.ContractInstance.STM             as InstanceState
import           Plutus.PAB.Effects.Contract                      (ContractDef, ContractEffect, ContractStore)
import qualified Plutus.PAB.Effects.Contract                      as Contract
import           Plutus.PAB.Effects.UUID                          (UUIDEffect, uuidNextRandom)
import           Plutus.PAB.Events.Contract                       (ContractInstanceId (..), ContractPABRequest (..),
                                                                   ContractResponse (..))
import qualified Plutus.PAB.Events.Contract                       as Events.Contract
import           Plutus.PAB.Types                                 (PABError (..))

-- | Create a new instance of the contract
activateContractSTM ::
    forall t m appBackend effs.
    ( Member (LogMsg (ContractInstanceMsg t)) effs
    , Member UUIDEffect effs
    , Member (ContractEffect t) effs
    , Member (ContractStore t) effs
    , Member (Reader InstancesState) effs
    , Contract.PABContract t
    , AppBackendConstraints t m appBackend
    , LastMember m (Reader ContractInstanceId ': appBackend)
    , LastMember m effs
    )
    => (Eff appBackend ~> IO)
    -> ContractDef t
    -> Eff effs ContractInstanceId
activateContractSTM runAppBackend contract = do
    activeContractInstanceId <- ContractInstanceId <$> uuidNextRandom
    logDebug @(ContractInstanceMsg t) $ InitialisingContract contract activeContractInstanceId
    initialState <- Contract.initialState @t contract
    Contract.putState @t contract activeContractInstanceId initialState
    s <- startSTMInstanceThread @t @m runAppBackend contract activeContractInstanceId
    ask >>= void . liftIO . STM.atomically . InstanceState.insertInstance activeContractInstanceId s
    logInfo @(ContractInstanceMsg t) $ ActivatedContractInstance contract activeContractInstanceId
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
    forall effs.
    ( Member ChainIndexEffect effs
    , Member WalletEffect effs
    , Member ContractRuntimeEffect effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    , Member (LogObserve (LogMessage Text.Text)) effs
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
        <> processWriteTxRequests @effs
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
    , Contract.PABContract t
    , AppBackendConstraints t m appBackend
    , LastMember m (Reader InstanceState ': Reader ContractInstanceId ': appBackend)
    )
    => (Eff appBackend ~> IO)
    -> ContractDef t
    -> ContractInstanceId
    -> Eff effs InstanceState
startSTMInstanceThread runAppBackend def instanceID = do
    state <- liftIO $ STM.atomically emptyInstanceState
    _ <- liftIO
        $ forkIO
        $ runAppBackend
        $ runReader instanceID
        $ runReader state
        $ stmInstanceLoop @t @m @(Reader InstanceState ': Reader ContractInstanceId ': appBackend) def instanceID

    pure state
    -- TODO: Separate chain index queries (non-blocking) from waiting for updates (blocking)

type AppBackendConstraints t m effs =
    ( LastMember m effs
    , MonadIO m
    , Member (Error PABError) effs
    , Member (LogMsg (ContractInstanceMsg t)) effs
    , Member ChainIndexEffect effs
    , Member WalletEffect effs
    , Member ContractRuntimeEffect effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    , Member (LogObserve (LogMessage Text.Text)) effs
    , Member (LogMsg TxBalanceMsg) effs
    , Member (Reader BlockchainEnv) effs
    , Member (ContractEffect t) effs
    , Member (ContractStore t) effs
    )

-- | Handle requests using 'respondToRequestsSTM' until the contract is done.
stmInstanceLoop ::
    forall t m effs.
    ( AppBackendConstraints t m effs
    , Member (Reader InstanceState) effs
    , Member (Reader ContractInstanceId) effs
    , Contract.PABContract t
    )
    => ContractDef t
    -> ContractInstanceId
    -> Eff effs ()
stmInstanceLoop def instanceId = do
    (currentState :: Contract.State t) <- Contract.getState @t instanceId
    let rqs = Contract.requests (Proxy @t) currentState
    updateState rqs
    case rqs of
        [] -> do
            ask >>= liftIO . STM.atomically . InstanceState.setActivity Done
        _ -> do
            response <- respondToRequestsSTM @t instanceId currentState
            event <- liftIO $ STM.atomically response
            (newState :: Contract.State t) <- Contract.updateContract @t def currentState event
            Contract.putState @t def instanceId newState
            stmInstanceLoop @t def instanceId

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
    ( Member ChainIndexEffect effs
    , Member WalletEffect effs
    , Member ContractRuntimeEffect effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    , Member (LogObserve (LogMessage Text.Text)) effs
    , Member (LogMsg (ContractInstanceMsg t)) effs
    , Member (LogMsg TxBalanceMsg) effs
    , Member (Reader ContractInstanceId) effs
    , Member (Reader BlockchainEnv) effs
    , Member (Reader InstanceState) effs
    , Contract.PABContract t
    )
    => ContractInstanceId
    -> Contract.State t
    -> Eff effs (STM (Response ContractResponse))
respondToRequestsSTM instanceId currentState = do
    let rqs = Contract.requests (Proxy @t) currentState
    logDebug @(ContractInstanceMsg t) $ HandlingRequests instanceId rqs
    tryHandler' stmRequestHandler rqs
