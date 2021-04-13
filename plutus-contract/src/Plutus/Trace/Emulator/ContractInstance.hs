{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-

The scheduler thread that runs a contract instance.

-}
module Plutus.Trace.Emulator.ContractInstance(
    contractThread
    , getThread
    , EmulatorRuntimeError
    , runInstance
    -- * Instance state
    , ContractInstanceState(..)
    , emptyInstanceState
    , addEventInstanceState
    -- * Internals
    , getHooks
    , addResponse
    ) where

import           Control.Lens
import           Control.Monad                        (guard, unless, void, when)
import           Control.Monad.Freer
import           Control.Monad.Freer.Coroutine        (Yield)
import           Control.Monad.Freer.Error            (Error, throwError)
import           Control.Monad.Freer.Extras.Log       (LogMessage, LogMsg (..), LogObserve, logDebug, logError, logInfo,
                                                       logWarn, mapLog)
import           Control.Monad.Freer.Extras.Modify    (raiseEnd)
import           Control.Monad.Freer.Reader           (Reader, ask, runReader)
import           Control.Monad.Freer.State            (State, evalState, get, gets, modify, put)
import           Data.Aeson                           (object)
import qualified Data.Aeson                           as JSON
import           Data.Foldable                        (traverse_)
import qualified Data.Text                            as T
import           Plutus.Contract                      (Contract (..), HasBlockchainActions)
import           Plutus.Contract.Resumable            (Request (..), Response (..))
import qualified Plutus.Contract.Resumable            as State
import           Plutus.Contract.Schema               (Event (..), Handlers (..), eventName, handlerName)
import           Plutus.Contract.Trace                (handleBlockchainQueries)
import           Plutus.Contract.Trace.RequestHandler (RequestHandler (..), RequestHandlerLogMsg, tryHandler,
                                                       wrapHandler)
import           Plutus.Contract.Types                (ResumableResult (..), logs, requests, resumableResult)
import           Plutus.Trace.Emulator.Types          (ContractConstraints, ContractHandle (..),
                                                       ContractInstanceLog (..), ContractInstanceMsg (..),
                                                       ContractInstanceState (..), ContractInstanceStateInternal (..),
                                                       EmulatedWalletEffects, EmulatedWalletEffects',
                                                       EmulatorAgentThreadEffs, EmulatorMessage (..),
                                                       EmulatorRuntimeError (..), EmulatorThreads,
                                                       addEventInstanceState, emptyInstanceState, instanceIdThreads,
                                                       toInstanceState)
import           Plutus.Trace.Scheduler               (AgentSystemCall, MessageCall (..), Priority (..), ThreadId,
                                                       mkAgentSysCall)
import qualified Wallet.API                           as WAPI
import           Wallet.Effects                       (ChainIndexEffect, ContractRuntimeEffect (..), NodeClientEffect,
                                                       WalletEffect)
import           Wallet.Emulator.LogMessages          (TxBalanceMsg)
import           Wallet.Types                         (ContractInstanceId, EndpointDescription (..), EndpointValue (..),
                                                       Notification (..), NotificationError (..))

-- | Effects available to threads that run in the context of specific
--   agents (ie wallets)
type ContractInstanceThreadEffs w s e effs =
    State (ContractInstanceStateInternal w s e ())
    ': Reader ContractInstanceId
    ': ContractRuntimeEffect
    ': LogMsg ContractInstanceMsg
    ': EmulatorAgentThreadEffs effs

-- | Handle 'ContractRuntimeEffect' by sending the notification to the
--   receiving contract's thread
handleContractRuntime ::
    forall effs2.
    ( Member (State EmulatorThreads) effs2
    , Member (Yield (AgentSystemCall EmulatorMessage) (Maybe EmulatorMessage)) effs2
    , Member (LogMsg ContractInstanceMsg) effs2
    , Member (Reader ThreadId) effs2
    )
    => Eff (ContractRuntimeEffect ': effs2)
    ~> Eff effs2
handleContractRuntime = interpret $ \case
    SendNotification n@Notification{notificationContractID} -> do
        logInfo $ SendingNotification n
        target <- gets (view $ instanceIdThreads . at notificationContractID)
        case target of
            Nothing -> do
                let e = InstanceDoesNotExist notificationContractID
                logWarn $ NotificationFailure e
                pure $ Just e
            Just threadId -> do
                ownId <- ask @ThreadId
                let Notification{notificationContractEndpoint=EndpointDescription ep, notificationContractArg} = n
                    vl = object ["tag" JSON..= ep, "value" JSON..= EndpointValue notificationContractArg]
                    e = Message threadId (EndpointCall ownId (EndpointDescription ep) vl)
                _ <- mkAgentSysCall @_ @EmulatorMessage Normal e
                logInfo $ NotificationSuccess n
                pure Nothing

-- | Start a new thread for a contract. Most of the work happens in
--   'runInstance'.
contractThread :: forall w s e effs.
    ( Member (State EmulatorThreads) effs
    , Member (Error EmulatorRuntimeError) effs
    , ContractConstraints s
    , HasBlockchainActions s
    , Show e
    , JSON.ToJSON e
    , JSON.ToJSON w
    , Monoid w
    )
    => ContractHandle w s e
    -> Eff (EmulatorAgentThreadEffs effs) ()
contractThread ContractHandle{chInstanceId, chContract, chInstanceTag} = do
    ask @ThreadId >>= registerInstance chInstanceId
    interpret (mapLog (\m -> ContractInstanceLog m chInstanceId chInstanceTag))
        $ handleContractRuntime
        $ runReader chInstanceId
        $ evalState (emptyInstanceState chContract)
        $ do
            logInfo Started
            logNewMessages @w @s @e
            logCurrentRequests @w @s @e
            msg <- mkAgentSysCall @_ @EmulatorMessage Normal WaitForMessage
            runInstance chContract msg

registerInstance :: forall effs.
    ( Member (State EmulatorThreads) effs )
    => ContractInstanceId
    -> ThreadId
    -> Eff effs ()
registerInstance i t = modify (instanceIdThreads . at i .~ Just t)

getThread :: forall effs.
    ( Member (State EmulatorThreads) effs
    , Member (Error EmulatorRuntimeError) effs
    )
    => ContractInstanceId
    -> Eff effs ThreadId
getThread t = do
    r <- gets (view $ instanceIdThreads . at t)
    maybe (throwError $ ThreadIdNotFound t) pure r

logStopped :: forall w s e effs.
    ( Member (LogMsg ContractInstanceMsg) effs
    , Show e
    )
    => ResumableResult w e (Event s) (Handlers s) ()
    -> Eff effs ()
logStopped ResumableResult{_finalState} =
    case _finalState of
        Left e  -> logWarn $ StoppedWithError $ show e
        Right _ -> logInfo $ StoppedNoError

-- | Run an instance of a contract
runInstance :: forall w s e effs.
    ( ContractConstraints s
    , HasBlockchainActions s
    , Member (Error EmulatorRuntimeError) effs
    , Show e
    , JSON.ToJSON e
    , JSON.ToJSON w
    , Monoid w
    )
    => Contract w s e ()
    -> Maybe EmulatorMessage
    -> Eff (ContractInstanceThreadEffs w s e effs) ()
runInstance contract event = do
    hks <- getHooks @w @s @e
    when (null hks) $
        gets @(ContractInstanceStateInternal w s e ()) (view resumableResult . cisiSuspState) >>= logStopped
    unless (null hks) $ do
        case event of
            Just Freeze -> do
                logInfo Freezing
                -- freeze ourselves, see note [Freeze and Thaw]
                mkAgentSysCall Frozen WaitForMessage >>= runInstance contract
            Just (EndpointCall _ _ vl) -> do
                logInfo $ ReceiveEndpointCall vl
                e <- decodeEvent @s vl
                _ <- respondToEvent @w @s @e e
                mkAgentSysCall Normal WaitForMessage >>= runInstance contract
            Just (ContractInstanceStateRequest sender) -> do
                state <- get @(ContractInstanceStateInternal w s e ())

                -- TODO: Maybe we should send it as a 'Dynamic' instead of
                -- JSON? It all stays in the same process, and it would save
                -- us having to convert to 'Value' and back.
                let stateJSON = JSON.toJSON $ toInstanceState state
                logInfo $ SendingContractState sender
                void $ mkAgentSysCall Normal (Message sender $ ContractInstanceStateResponse stateJSON)
                mkAgentSysCall Normal WaitForMessage >>= runInstance contract
            _ -> do
                response <- respondToRequest @w @s @e handleBlockchainQueries
                let prio =
                        maybe
                            -- If no events could be handled we go to sleep
                            -- with the lowest priority, waking only after
                            -- some external event has happened, for example
                            -- when a new block was added.
                            Sleeping

                            -- If an event was handled we go to sleep with
                            -- the 'Normal' priority, trying again after all
                            -- other active threads have had their turn
                            (const Normal)
                            response
                mkAgentSysCall prio WaitForMessage >>= runInstance contract

decodeEvent ::
    forall s effs.
    ( ContractConstraints s
    , Member (LogMsg ContractInstanceMsg) effs
    , Member (Error EmulatorRuntimeError) effs
    )
    => JSON.Value
    -> Eff effs (Event s)
decodeEvent vl =
    case JSON.fromJSON @(Event s) vl of
            JSON.Error e'       -> do
                let msg = JSONDecodingError e'
                logError $ InstErr msg
                throwError msg
            JSON.Success event' -> pure event'

getHooks :: forall w s e effs. Member (State (ContractInstanceStateInternal w s e ())) effs => Eff effs [Request (Handlers s)]
getHooks = gets @(ContractInstanceStateInternal w s e ()) (State.unRequests . view requests . view resumableResult . cisiSuspState)

-- | Add a 'Response' to the contract instance state
addResponse
    :: forall w s e effs.
    ( Member (State (ContractInstanceStateInternal w s e ())) effs
    , Member (LogMsg ContractInstanceMsg) effs
    , Monoid w
    )
    => Response (Event s)
    -> Eff effs ()
addResponse e = do
    oldState <- get @(ContractInstanceStateInternal w s e ())
    let newState = addEventInstanceState e oldState
    traverse_ put newState
    logNewMessages @w @s @e

type ContractInstanceRequests effs =
        Reader ContractInstanceId
         ': ContractRuntimeEffect
         ': (EmulatedWalletEffects' effs)

-- | Respond to a specific event
respondToEvent ::
    forall w s e effs.
    ( Member (State (ContractInstanceStateInternal w s e ())) effs
    , Members EmulatedWalletEffects effs
    , Member ContractRuntimeEffect effs
    , Member (Reader ContractInstanceId) effs
    , Member (LogMsg ContractInstanceMsg) effs
    , ContractConstraints s
    , Monoid w
    )
    => Event s
    -> Eff effs (Maybe (Response (Event s)))
respondToEvent e =
    respondToRequest @w @s @e $ RequestHandler $ \h -> do
        guard $ handlerName h == eventName e
        pure e

-- | Inspect the open requests of a contract instance,
--   and maybe respond to them. Returns the response that was provided to the
--   contract, if any.
respondToRequest :: forall w s e effs.
    ( Member (State (ContractInstanceStateInternal w s e ())) effs
    , Member ContractRuntimeEffect effs
    , Member (Reader ContractInstanceId) effs
    , Member (LogMsg ContractInstanceMsg) effs
    , Members EmulatedWalletEffects effs
    , ContractConstraints s
    , Monoid w
    )
    => RequestHandler (Reader ContractInstanceId ': ContractRuntimeEffect ': EmulatedWalletEffects) (Handlers s) (Event s)
    -- ^ How to respond to the requests.
    ->  Eff effs (Maybe (Response (Event s)))
respondToRequest f = do
    hks <- getHooks @w @s @e
    let hdl :: (Eff (Reader ContractInstanceId ': ContractRuntimeEffect ': EmulatedWalletEffects) (Maybe (Response (Event s)))) = tryHandler (wrapHandler f) hks
        hdl' :: (Eff (ContractInstanceRequests effs) (Maybe (Response (Event s)))) = raiseEnd hdl

        response_ :: Eff effs (Maybe (Response (Event s))) =
                subsume @(LogMsg T.Text)
                    $ subsume @(LogMsg TxBalanceMsg)
                    $ subsume @(LogMsg RequestHandlerLogMsg)
                    $ subsume @(LogObserve (LogMessage T.Text))
                    $ subsume @ChainIndexEffect
                    $ subsume @NodeClientEffect
                    $ subsume @(Error WAPI.WalletAPIError)
                    $ subsume @WalletEffect
                    $ subsume @ContractRuntimeEffect
                    $ subsume @(Reader ContractInstanceId) hdl'
    response <- response_
    traverse_ (addResponse @w @s @e) response
    logResponse @w @s @e response
    pure response

---
-- Logging
---

logResponse ::  forall w s e effs.
    ( ContractConstraints s
    , Member (LogMsg ContractInstanceMsg) effs
    , Member (State (ContractInstanceStateInternal w s e ())) effs
    )
    => Maybe (Response (Event s))
    -> Eff effs ()
logResponse = \case
    Nothing -> logDebug NoRequestsHandled
    Just rsp -> do
        logDebug $ HandledRequest $ fmap JSON.toJSON rsp
        logCurrentRequests @w @s @e

logCurrentRequests :: forall w s e effs.
    ( ContractConstraints s
    , Member (State (ContractInstanceStateInternal w s e ())) effs
    , Member (LogMsg ContractInstanceMsg) effs
    )
    => Eff effs ()
logCurrentRequests = do
    hks <- getHooks @w @s @e
    logDebug $ CurrentRequests $ fmap (fmap JSON.toJSON) hks

-- | Take the new log messages that were produced by the contract
--   instance and log them with the 'LogMsg' effect.
logNewMessages :: forall w s e effs.
    ( Member (LogMsg ContractInstanceMsg) effs
    , Member (State (ContractInstanceStateInternal w s e ())) effs
    )
    => Eff effs ()
logNewMessages = do
    newContractLogs <- gets @(ContractInstanceStateInternal w s e ()) (view (resumableResult . logs) . cisiSuspState)
    traverse_ (send . LMessage . fmap ContractLog) newContractLogs
