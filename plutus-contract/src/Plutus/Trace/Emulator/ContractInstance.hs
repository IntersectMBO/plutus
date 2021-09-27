{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
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
    -- * Indexed block
    , IndexedBlock(..)
    , indexBlock
    -- * Internals
    , getHooks
    , addResponse
    ) where

import           Control.Lens
import           Control.Monad                        (guard, join, unless, void, when)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error            (Error, throwError)
import           Control.Monad.Freer.Extras.Log       (LogMessage, LogMsg (..), LogObserve, logDebug, logError, logInfo,
                                                       logWarn, mapLog)
import           Control.Monad.Freer.Extras.Modify    (raiseEnd)
import           Control.Monad.Freer.Reader           (Reader, ask, runReader)
import           Control.Monad.Freer.State            (State, evalState, get, gets, modify, put)
import qualified Data.Aeson                           as JSON
import           Data.Foldable                        (traverse_)
import           Data.List.NonEmpty                   (NonEmpty (..))
import           Data.Map                             (Map)
import qualified Data.Map                             as Map
import           Data.Maybe                           (listToMaybe, mapMaybe)
import qualified Data.Set                             as Set
import qualified Data.Text                            as T
import           Ledger.Blockchain                    (OnChainTx (..))
import           Ledger.Tx                            (Address, TxIn (..), TxOut (..), TxOutRef, txId)
import           Plutus.ChainIndex                    (ChainIndexQueryEffect, ChainIndexTx, TxStatus (..),
                                                       TxValidity (..), _ValidTx, citxInputs, citxOutputs,
                                                       fromOnChainTx)
import           Plutus.Contract                      (Contract (..))
import           Plutus.Contract.Effects              (PABReq, PABResp (AwaitTxStatusChangeResp), matches)
import qualified Plutus.Contract.Effects              as E
import           Plutus.Contract.Resumable            (Request (..), Response (..))
import qualified Plutus.Contract.Resumable            as State
import           Plutus.Contract.Trace                (handleBlockchainQueries)
import           Plutus.Contract.Trace.RequestHandler (RequestHandler (..), RequestHandlerLogMsg, tryHandler,
                                                       wrapHandler)
import           Plutus.Contract.Types                (ResumableResult (..), lastLogs, requests, resumableResult)
import           Plutus.Trace.Emulator.Types          (ContractConstraints, ContractHandle (..),
                                                       ContractInstanceLog (..), ContractInstanceMsg (..),
                                                       ContractInstanceState (..), ContractInstanceStateInternal (..),
                                                       EmulatedWalletEffects, EmulatedWalletEffects',
                                                       EmulatorAgentThreadEffs, EmulatorMessage (..),
                                                       EmulatorRuntimeError (..), EmulatorThreads,
                                                       addEventInstanceState, emptyInstanceState, instanceIdThreads,
                                                       toInstanceState)
import           Plutus.Trace.Scheduler               (MessageCall (..), Priority (..), ThreadId, mkAgentSysCall)
import qualified Wallet.API                           as WAPI
import           Wallet.Effects                       (NodeClientEffect, WalletEffect)
import           Wallet.Emulator.LogMessages          (TxBalanceMsg)
import           Wallet.Types                         (ContractInstanceId)

-- | Effects available to threads that run in the context of specific
--   agents (ie wallets)
type ContractInstanceThreadEffs w s e effs =
    State (ContractInstanceStateInternal w s e ())
    ': Reader ContractInstanceId
    ': LogMsg ContractInstanceMsg
    ': EmulatorAgentThreadEffs effs

-- | Start a new thread for a contract. Most of the work happens in
--   'runInstance'.
contractThread :: forall w s e effs.
    ( Member (State EmulatorThreads) effs
    , Member (Error EmulatorRuntimeError) effs
    , ContractConstraints s
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
        $ runReader chInstanceId
        $ evalState (emptyInstanceState chContract)
        $ do
            logInfo Started
            logNewMessages @w @s @e
            logCurrentRequests @w @s @e
            msg <- mkAgentSysCall @_ @EmulatorMessage Normal WaitForMessage
            runInstance chContract msg
            runInstanceObservableState chContract msg

registerInstance :: forall effs.
    ( Member (State EmulatorThreads) effs )
    => ContractInstanceId
    -> ThreadId
    -> Eff effs ()
registerInstance i t = modify (instanceIdThreads . at i ?~ t)

getThread :: forall effs.
    ( Member (State EmulatorThreads) effs
    , Member (Error EmulatorRuntimeError) effs
    )
    => ContractInstanceId
    -> Eff effs ThreadId
getThread t = do
    r <- gets (view $ instanceIdThreads . at t)
    maybe (throwError $ ThreadIdNotFound t) pure r

logStopped :: forall w e effs.
    ( Member (LogMsg ContractInstanceMsg) effs
    , Show e
    )
    => ResumableResult w e PABResp PABReq ()
    -> Eff effs ()
logStopped ResumableResult{_finalState} =
    case _finalState of
        Left e  -> logWarn $ StoppedWithError $ show e
        Right _ -> logInfo StoppedNoError

-- | Run an instance of a contract
runInstance :: forall w s e effs.
    ( ContractConstraints s
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
    unless (null hks) $
        case event of
            Just Freeze -> do
                logInfo Freezing
                -- freeze ourselves, see note [Freeze and Thaw]
                mkAgentSysCall Frozen WaitForMessage >>= runInstance contract
            Just (EndpointCall _ desc vl) -> do
                logInfo $ ReceiveEndpointCall desc vl
                e <- decodeEvent vl
                _ <- respondToEvent @w @s @e e
                mkAgentSysCall Normal WaitForMessage >>= runInstance contract
            Just (ContractInstanceStateRequest sender) -> do
                handleObservableStateRequest sender
                mkAgentSysCall Normal WaitForMessage >>= runInstance contract
            Just (NewSlot block _) -> do
                processNewTransactions @w @s @e (join block)
                runInstance contract Nothing
            _ -> waitForNextMessage True >>= runInstance contract

-- | Run an instance to only answer to observable state requests even when the
-- contract has stopped.
runInstanceObservableState :: forall w s e effs.
    ( ContractConstraints s
    , Member (Error EmulatorRuntimeError) effs
    , Show e
    , JSON.ToJSON e
    , JSON.ToJSON w
    , Monoid w
    )
    => Contract w s e ()
    -> Maybe EmulatorMessage
    -> Eff (ContractInstanceThreadEffs w s e effs) ()
runInstanceObservableState contract event = do
    case event of
        Just (ContractInstanceStateRequest sender) -> do
            handleObservableStateRequest sender
            mkAgentSysCall Normal WaitForMessage >>= runInstanceObservableState contract
        _ -> waitForNextMessage False >>= runInstanceObservableState contract

-- | Contract instance state request handler.
handleObservableStateRequest :: forall w s e effs.
    ( JSON.ToJSON e
    , JSON.ToJSON w
    )
    => ThreadId -- ^ Thread ID sending the request
    -> Eff (ContractInstanceThreadEffs w s e effs) ()
handleObservableStateRequest sender = do
    state <- get @(ContractInstanceStateInternal w s e ())

    -- TODO: Maybe we should send it as a 'Dynamic' instead of
    -- JSON? It all stays in the same process, and it would save
    -- us having to convert to 'Value' and back.
    let stateJSON = JSON.toJSON $ toInstanceState state
    logInfo $ SendingContractState sender
    void $ mkAgentSysCall Normal (Message sender $ ContractInstanceStateResponse stateJSON)

-- | Wait for the next emulator message.
waitForNextMessage :: forall w s e effs.
    ( Monoid w
    )
    => Bool -- ^ Flag on whether to log 'NoRequestsHandled' messages
    -> Eff (ContractInstanceThreadEffs w s e effs) (Maybe EmulatorMessage)
waitForNextMessage isLogShowed = do
    response <- respondToRequest @w @s @e isLogShowed handleBlockchainQueries
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
    mkAgentSysCall prio WaitForMessage

decodeEvent ::
    forall effs.
    ( Member (LogMsg ContractInstanceMsg) effs
    , Member (Error EmulatorRuntimeError) effs
    )
    => JSON.Value
    -> Eff effs PABResp
decodeEvent vl =
    case JSON.fromJSON @PABResp vl of
            JSON.Error e'       -> do
                let msg = EmulatorJSONDecodingError e' vl
                logError $ InstErr msg
                throwError msg
            JSON.Success event' -> pure event'

getHooks :: forall w s e effs. Member (State (ContractInstanceStateInternal w s e ())) effs => Eff effs [Request PABReq]
getHooks = gets @(ContractInstanceStateInternal w s e ()) (State.unRequests . view requests . view resumableResult . cisiSuspState)

-- | Update the contract instance with information from the new block.
processNewTransactions ::
    forall w s e effs.
    ( Member (State (ContractInstanceStateInternal w s e ())) effs
    , Member (LogMsg ContractInstanceMsg) effs
    , Monoid w
    )
    => [OnChainTx]
    -> Eff effs ()
processNewTransactions txns = do
    updateTxStatus @w @s @e txns

    let blck = indexBlock $ fmap fromOnChainTx txns
    updateTxOutSpent @w @s @e blck
    updateTxOutProduced @w @s @e blck

-- | Update the contract instance with transaction status information from the
--   new block.
updateTxStatus ::
    forall w s e effs.
    ( Member (State (ContractInstanceStateInternal w s e ())) effs
    , Member (LogMsg ContractInstanceMsg) effs
    , Monoid w
    )
    => [OnChainTx]
    -> Eff effs ()
updateTxStatus txns = do
    -- Check whether the contract instance is waiting for a status change of any
    -- of the new transactions. If that is the case, call 'addResponse' to send the
    -- response.
    let txWithStatus (Invalid tx) = (txId tx, TxInvalid)
        txWithStatus (Valid tx)   = (txId tx, TxValid)
        statusMap = Map.fromList $ fmap txWithStatus txns
    hks <- mapMaybe (traverse (preview E._AwaitTxStatusChangeReq)) <$> getHooks @w @s @e
    let mpReq Request{rqID, itID, rqRequest=txid} =
            case Map.lookup txid statusMap of
                Nothing -> Nothing
                Just newStatus -> Just Response{rspRqID=rqID, rspItID=itID, rspResponse=AwaitTxStatusChangeResp txid (Committed newStatus)}
        txStatusHk = listToMaybe $ mapMaybe mpReq hks
    traverse_ (addResponse @w @s @e) txStatusHk
    logResponse @w @s @e False txStatusHk

-- | Update the contract instance with transaction output information from the
--   new block.
updateTxOutProduced ::
    forall w s e effs.
    ( Member (State (ContractInstanceStateInternal w s e ())) effs
    , Member (LogMsg ContractInstanceMsg) effs
    , Monoid w
    )
    => IndexedBlock
    -> Eff effs ()
updateTxOutProduced IndexedBlock{ibUtxoProduced} = do
    -- Check whether the contract instance is waiting for address changes
    hks <- mapMaybe (traverse (preview E._AwaitUtxoProducedReq)) <$> getHooks @w @s @e
    let mpReq Request{rqID, itID, rqRequest=addr} =
            case Map.lookup addr ibUtxoProduced of
                Nothing      -> Nothing
                Just newTxns -> Just Response{rspRqID=rqID, rspItID=itID, rspResponse=E.AwaitUtxoProducedResp newTxns}
        utxoResp = listToMaybe $ mapMaybe mpReq hks
    traverse_ (addResponse @w @s @e) utxoResp
    logResponse @w @s @e False utxoResp

-- | Update the contract instance with transaction input information from the
--   new block.
updateTxOutSpent ::
    forall w s e effs.
    ( Member (State (ContractInstanceStateInternal w s e ())) effs
    , Member (LogMsg ContractInstanceMsg) effs
    , Monoid w
    )
    => IndexedBlock
    -> Eff effs ()
updateTxOutSpent IndexedBlock{ibUtxoSpent} = do
    -- Check whether the contract instance is waiting for address changes
    hks <- mapMaybe (traverse (preview E._AwaitUtxoSpentReq)) <$> getHooks @w @s @e
    let mpReq Request{rqID, itID, rqRequest=addr} =
            case Map.lookup addr ibUtxoSpent of
                Nothing      -> Nothing
                Just newTxns -> Just Response{rspRqID=rqID, rspItID=itID, rspResponse=E.AwaitUtxoSpentResp newTxns}
        utxoResp = listToMaybe $ mapMaybe mpReq hks
    traverse_ (addResponse @w @s @e) utxoResp
    logResponse @w @s @e False utxoResp

-- | Add a 'Response' to the contract instance state
addResponse
    :: forall w s e effs.
    ( Member (State (ContractInstanceStateInternal w s e ())) effs
    , Member (LogMsg ContractInstanceMsg) effs
    , Monoid w
    )
    => Response PABResp
    -> Eff effs ()
addResponse e = do
    oldState <- get @(ContractInstanceStateInternal w s e ())
    let newState = addEventInstanceState e oldState
    traverse_ put newState
    logNewMessages @w @s @e

type ContractInstanceRequests effs =
        Reader ContractInstanceId
         ': EmulatedWalletEffects' effs

-- | Respond to a specific event
respondToEvent ::
    forall w s e effs.
    ( Member (State (ContractInstanceStateInternal w s e ())) effs
    , Members EmulatedWalletEffects effs
    , Member (Reader ContractInstanceId) effs
    , Member (LogMsg ContractInstanceMsg) effs
    , Monoid w
    )
    => PABResp
    -> Eff effs (Maybe (Response PABResp))
respondToEvent e = respondToRequest @w @s @e True $ RequestHandler $ \h -> do
    guard $ h `matches` e
    pure e

-- | Inspect the open requests of a contract instance,
--   and maybe respond to them. Returns the response that was provided to the
--   contract, if any.
respondToRequest :: forall w s e effs.
    ( Member (State (ContractInstanceStateInternal w s e ())) effs
    , Member (Reader ContractInstanceId) effs
    , Member (LogMsg ContractInstanceMsg) effs
    , Members EmulatedWalletEffects effs
    , Monoid w
    )
    => Bool -- ^ Flag on whether to log 'NoRequestsHandled' messages.
    -> RequestHandler (Reader ContractInstanceId ': EmulatedWalletEffects) PABReq PABResp
    -- ^ How to respond to the requests.
    -> Eff effs (Maybe (Response PABResp))
respondToRequest isLogShowed f = do
    hks <- getHooks @w @s @e
    let hdl :: (Eff (Reader ContractInstanceId ': EmulatedWalletEffects) (Maybe (Response PABResp))) = tryHandler (wrapHandler f) hks
        hdl' :: (Eff (ContractInstanceRequests effs) (Maybe (Response PABResp))) = raiseEnd hdl

        response_ :: Eff effs (Maybe (Response PABResp)) =
            subsume @(LogMsg T.Text)
                    $ subsume @(LogMsg TxBalanceMsg)
                    $ subsume @(LogMsg RequestHandlerLogMsg)
                    $ subsume @(LogObserve (LogMessage T.Text))
                    $ subsume @ChainIndexQueryEffect
                    $ subsume @NodeClientEffect
                    $ subsume @(Error WAPI.WalletAPIError)
                    $ subsume @WalletEffect
                    $ subsume @(Reader ContractInstanceId) hdl'
    response <- response_
    traverse_ (addResponse @w @s @e) response
    logResponse @w @s @e isLogShowed response
    pure response

---
-- Logging
---

logResponse ::  forall w s e effs.
    ( Member (LogMsg ContractInstanceMsg) effs
    , Member (State (ContractInstanceStateInternal w s e ())) effs
    )
    => Bool -- ^ Flag on whether to log 'NoRequestsHandled' messages
    -> Maybe (Response PABResp)
    -> Eff effs ()
logResponse isLogShowed = \case
    Nothing -> when isLogShowed $ logDebug NoRequestsHandled
    Just rsp -> do
        logDebug $ HandledRequest $ fmap JSON.toJSON rsp
        logCurrentRequests @w @s @e

logCurrentRequests :: forall w s e effs.
    ( Member (State (ContractInstanceStateInternal w s e ())) effs
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
    newContractLogs <- gets @(ContractInstanceStateInternal w s e ()) (view (resumableResult . lastLogs) . cisiSuspState)
    traverse_ (send . LMessage . fmap ContractLog) newContractLogs

-- | A block of transactions, indexed by tx outputs spent and by
--   addresses on which new outputs are produced
data IndexedBlock =
  IndexedBlock
    { ibUtxoSpent    :: Map TxOutRef ChainIndexTx
    , ibUtxoProduced :: Map Address (NonEmpty ChainIndexTx)
    }

instance Semigroup IndexedBlock where
  l <> r =
    IndexedBlock
      { ibUtxoSpent = ibUtxoSpent l <> ibUtxoSpent r
      , ibUtxoProduced = Map.unionWith (<>) (ibUtxoProduced l) (ibUtxoProduced r)
      }

instance Monoid IndexedBlock where
  mempty = IndexedBlock mempty mempty

indexBlock :: [ChainIndexTx] -> IndexedBlock
indexBlock = foldMap indexTx where
  indexTx otx =
    IndexedBlock
      { ibUtxoSpent = Map.fromSet (const otx) $ Set.map txInRef $ view citxInputs otx
      , ibUtxoProduced = Map.fromListWith (<>) $ view (citxOutputs . _ValidTx) otx >>= (\TxOut{txOutAddress} -> [(txOutAddress, otx :| [])])
      }
