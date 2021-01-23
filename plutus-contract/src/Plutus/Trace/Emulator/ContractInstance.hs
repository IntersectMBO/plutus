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
    -- * Instance state
    , ContractInstanceState(..)
    , emptyInstanceState
    , addEventInstanceState
    ) where

import           Control.Lens
import           Control.Monad                                 (guard, unless, void, when)
import           Control.Monad.Freer
import           Control.Monad.Freer.Coroutine                 (Yield)
import           Control.Monad.Freer.Error                     (Error, throwError)
import           Control.Monad.Freer.Extras                    (raiseEnd11)
import           Control.Monad.Freer.Log                       (LogMessage, LogMsg (..), LogObserve, logDebug, logError,
                                                                logInfo, logWarn, mapLog)
import           Control.Monad.Freer.Reader                    (Reader, ask, runReader)
import           Control.Monad.Freer.State                     (State, evalState, get, gets, modify, put)
import           Data.Aeson                                    (object)
import qualified Data.Aeson                                    as JSON
import           Data.Foldable                                 (traverse_)
import           Data.Sequence                                 (Seq)
import qualified Data.Sequence                                 as Seq
import qualified Data.Text                                     as T
import           Language.Plutus.Contract                      (Contract (..), HasBlockchainActions)
import           Language.Plutus.Contract.Resumable            (Request (..), Response (..))
import qualified Language.Plutus.Contract.Resumable            as State
import           Language.Plutus.Contract.Schema               (Event (..), Handlers (..), eventName, handlerName)
import           Language.Plutus.Contract.Trace                (handleBlockchainQueries)
import           Language.Plutus.Contract.Trace.RequestHandler (RequestHandler (..), RequestHandlerLogMsg, tryHandler,
                                                                wrapHandler)
import           Language.Plutus.Contract.Types                (ResumableResult (..))
import           Plutus.Trace.Emulator.Types                   (ContractConstraints, ContractHandle (..),
                                                                ContractInstanceLog (..), ContractInstanceMsg (..),
                                                                ContractInstanceState (..), EmulatorAgentThreadEffs,
                                                                EmulatorMessage (..), EmulatorRuntimeError (..),
                                                                EmulatorThreads, addEventInstanceState,
                                                                emptyInstanceState, instanceIdThreads)
import           Plutus.Trace.Scheduler                        (Priority (..), SysCall (..), SystemCall, ThreadId,
                                                                mkSysCall, sleep)
import qualified Wallet.API                                    as WAPI
import           Wallet.Effects                                (ChainIndexEffect, ContractRuntimeEffect (..),
                                                                NodeClientEffect, SigningProcessEffect, WalletEffect)
import           Wallet.Emulator.LogMessages                   (TxBalanceMsg)
import           Wallet.Emulator.MultiAgent                    (EmulatedWalletEffects, MultiAgentEffect, walletAction)
import           Wallet.Emulator.Wallet                        (Wallet)
import           Wallet.Types                                  (ContractInstanceId, EndpointDescription (..),
                                                                EndpointValue (..), Notification (..),
                                                                NotificationError (..))

-- | Effects available to threads that run in the context of specific
--   agents (ie wallets)
type ContractInstanceThreadEffs s e effs =
    State (ContractInstanceState s e ())
    ': Reader ContractInstanceId
    ': ContractRuntimeEffect
    ': LogMsg ContractInstanceMsg
    ': EmulatorAgentThreadEffs effs

-- | Handle 'ContractRuntimeEffect' by sending the notification to the
--   receiving contract's thread
handleContractRuntime ::
    forall effs effs2.
    ( Member (State EmulatorThreads) effs2
    , Member (Yield (SystemCall effs EmulatorMessage) (Maybe EmulatorMessage)) effs2
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
                _ <- mkSysCall @effs @EmulatorMessage Normal e
                logInfo $ NotificationSuccess n
                pure Nothing

-- | Start a new thread for a contract. Most of the work happens in
--   'runInstance'.
contractThread :: forall s e effs.
    ( Member (State EmulatorThreads) effs
    , Member MultiAgentEffect effs
    , Member (Error EmulatorRuntimeError) effs
    , ContractConstraints s
    , HasBlockchainActions s
    , Show e
    , JSON.ToJSON e
    )
    => ContractHandle s e
    -> Eff (EmulatorAgentThreadEffs effs) ()
contractThread ContractHandle{chInstanceId, chContract, chInstanceTag} = do
    ask @ThreadId >>= registerInstance chInstanceId
    interpret (mapLog (\m -> ContractInstanceLog m chInstanceId chInstanceTag))
        $ handleContractRuntime @effs
        $ runReader chInstanceId
        $ evalState (emptyInstanceState chContract)
        $ do
            logInfo Started
            logNewMessages @s @e Seq.empty
            logCurrentRequests @s @e
            msg <- mkSysCall @effs @EmulatorMessage Normal Suspend
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

logStopped :: forall s e effs.
    ( Member (LogMsg ContractInstanceMsg) effs
    , Show e
    )
    => ResumableResult e (Event s) (Handlers s) ()
    -> Eff effs ()
logStopped ResumableResult{wcsFinalState} =
    case wcsFinalState of
        Left e  -> logWarn $ StoppedWithError $ show e
        Right _ -> logInfo $ StoppedNoError

-- | Run an instance of a contract
runInstance :: forall s e effs.
    ( Member MultiAgentEffect effs
    , ContractConstraints s
    , HasBlockchainActions s
    , Member (Error EmulatorRuntimeError) effs
    , Show e
    , JSON.ToJSON e
    )
    => Contract s e ()
    -> Maybe EmulatorMessage
    -> Eff (ContractInstanceThreadEffs s e effs) ()
runInstance contract event = do
    hks <- getHooks @s @e
    when (null hks) $
        gets @(ContractInstanceState s e ()) instContractState >>= logStopped
    unless (null hks) $ do
        case event of
            Just Freeze -> do
                logInfo Freezing
                -- freeze ourselves, see note [Freeze and Thaw]
                sleep @effs Frozen >>= runInstance contract
            Just (EndpointCall _ _ vl) -> do
                logInfo $ ReceiveEndpointCall vl
                e <- decodeEvent @s vl
                _ <- respondToEvent @s @e contract e
                sleep @effs Normal >>= runInstance contract
            Just (ContractInstanceStateRequest sender) -> do
                state <- get @(ContractInstanceState s e ())
                let stateJSON = JSON.toJSON state
                logInfo $ SendingContractState sender
                void $ mkSysCall @effs @EmulatorMessage Normal (Message sender $ ContractInstanceStateResponse stateJSON)
                sleep @effs Normal >>= runInstance contract
            _ -> do
                response <- respondToRequest @s @e contract handleBlockchainQueries
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
                sleep @effs prio >>= runInstance contract

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

getHooks :: forall s e effs. Member (State (ContractInstanceState s e ())) effs => Eff effs [Request (Handlers s)]
getHooks = State.unRequests . wcsRequests <$> gets @(ContractInstanceState s e ()) instContractState

-- | Add a 'Response' to the contract instance state
addResponse
    :: forall s e effs.
    ( Member (State (ContractInstanceState s e ())) effs
    , Member (LogMsg ContractInstanceMsg) effs
    )
    => Contract s e ()
    -> Response (Event s)
    -> Eff effs ()
addResponse contract e = do
    oldState <- get @(ContractInstanceState s e ())
    let newState = addEventInstanceState contract e oldState
    put newState
    logNewMessages @s @e (wcsLogs $ instContractState oldState)

raiseWallet :: forall f effs.
    ( Member f EmulatedWalletEffects
    , Member MultiAgentEffect effs
    )
    => Wallet
    -> f
    ~> Eff effs
raiseWallet wllt = walletAction wllt . send

type ContractInstanceRequests effs =
        Reader ContractInstanceId
         ': ContractRuntimeEffect
         ': WalletEffect
         ': Error WAPI.WalletAPIError
         ': NodeClientEffect
         ': ChainIndexEffect
         ': SigningProcessEffect
         ': LogObserve (LogMessage T.Text)
         ': LogMsg RequestHandlerLogMsg
         ': LogMsg TxBalanceMsg
         ': LogMsg T.Text
         ': effs

-- | Respond to a specific event
respondToEvent ::
    forall s e effs.
    ( Member (State (ContractInstanceState s e ())) effs
    , Member MultiAgentEffect effs
    , Member (Reader Wallet) effs
    , Member ContractRuntimeEffect effs
    , Member (Reader ContractInstanceId) effs
    , Member (LogMsg ContractInstanceMsg) effs
    , ContractConstraints s
    )
    => Contract s e ()
    -> Event s
    -> Eff effs (Maybe (Response (Event s)))
respondToEvent contract e =
    respondToRequest @s @e contract $ RequestHandler $ \h -> do
        guard $ handlerName h == eventName e
        pure e

-- | Inspect the open requests of a contract instance,
--   and maybe respond to them. Returns the response that was provided to the
--   contract, if any.
respondToRequest :: forall s e effs.
    ( Member (State (ContractInstanceState s e ())) effs
    , Member MultiAgentEffect effs
    , Member (Reader Wallet) effs
    , Member ContractRuntimeEffect effs
    , Member (Reader ContractInstanceId) effs
    , Member (LogMsg ContractInstanceMsg) effs
    , ContractConstraints s
    )
    => Contract s e ()
    -> RequestHandler (Reader ContractInstanceId ': ContractRuntimeEffect ': EmulatedWalletEffects) (Handlers s) (Event s)
    -- ^ How to respond to the requests.
    ->  Eff effs (Maybe (Response (Event s)))
respondToRequest contract f = do
    hks <- getHooks @s @e
    ownWallet <- ask @Wallet
    let hdl :: (Eff (Reader ContractInstanceId ': ContractRuntimeEffect ': EmulatedWalletEffects) (Maybe (Response (Event s)))) = tryHandler (wrapHandler f) hks
        hdl' :: (Eff (ContractInstanceRequests effs) (Maybe (Response (Event s)))) = raiseEnd11 hdl

        response_ :: Eff effs (Maybe (Response (Event s))) =
            interpret (raiseWallet @(LogMsg T.Text) ownWallet)
                $ interpret (raiseWallet @(LogMsg TxBalanceMsg) ownWallet)
                $ interpret (raiseWallet @(LogMsg RequestHandlerLogMsg) ownWallet)
                $ interpret (raiseWallet @(LogObserve (LogMessage T.Text)) ownWallet)
                $ interpret (raiseWallet @SigningProcessEffect ownWallet)
                $ interpret (raiseWallet @ChainIndexEffect ownWallet)
                $ interpret (raiseWallet @NodeClientEffect ownWallet)
                $ interpret (raiseWallet @(Error WAPI.WalletAPIError) ownWallet)
                $ interpret (raiseWallet @WalletEffect ownWallet)
                $ subsume @ContractRuntimeEffect
                $ subsume @(Reader ContractInstanceId) hdl'
    response <- response_
    traverse_ (addResponse @s @e contract) response
    logResponse @s @e response
    pure response

---
-- Logging
---

logResponse ::  forall s e effs.
    ( ContractConstraints s
    , Member (LogMsg ContractInstanceMsg) effs
    , Member (State (ContractInstanceState s e ())) effs
    )
    => Maybe (Response (Event s))
    -> Eff effs ()
logResponse = \case
    Nothing -> logDebug NoRequestsHandled
    Just rsp -> do
        logDebug $ HandledRequest $ fmap JSON.toJSON rsp
        logCurrentRequests @s @e

logCurrentRequests :: forall s e effs.
    ( ContractConstraints s
    , Member (State (ContractInstanceState s e ())) effs
    , Member (LogMsg ContractInstanceMsg) effs
    )
    => Eff effs ()
logCurrentRequests = do
    hks <- getHooks @s @e
    logDebug $ CurrentRequests $ fmap (fmap JSON.toJSON) hks

-- | Take the new log messages that were produced by the contract
--   instance and log them with the 'LogMsg' effect.
logNewMessages :: forall s e effs.
    ( Member (LogMsg ContractInstanceMsg) effs
    , Member (State (ContractInstanceState s e ())) effs
    )
    => Seq (LogMessage JSON.Value) -- old messages
    -> Eff effs ()
logNewMessages oldMessages = do
    newState <- get @(ContractInstanceState s e ())
    let contractLogs = wcsLogs $ instContractState newState
        newContractLogs = Seq.drop (Seq.length oldMessages) contractLogs
    traverse_ (send . LMessage . fmap ContractLog) newContractLogs
