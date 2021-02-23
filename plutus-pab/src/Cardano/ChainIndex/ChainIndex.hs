{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module Cardano.ChainIndex.ChainIndex
    ( processIndexEffects
    , startWatching
    , watchedAddresses
    , confirmedBlocks
    , syncState
    , updateThread
    , fetchNewBlocks
    , healthcheck
    ) where

import           Cardano.BM.Data.Trace            (Trace)
import           Cardano.Node.Types               (FollowerID, NodeFollowerEffect, getBlocks, getSlot, newFollower)
import           Control.Concurrent               (threadDelay)
import           Control.Concurrent.MVar          (MVar, putMVar, takeMVar)
import           Control.Monad                    (forever, unless)
import           Control.Monad.Freer              hiding (run)
import           Control.Monad.Freer.Extras.Log
import           Control.Monad.Freer.Extras.State (assign, use)
import           Control.Monad.Freer.State
import qualified Control.Monad.Freer.State        as Eff
import           Control.Monad.IO.Class           (MonadIO (..))
import           Data.Foldable                    (fold, traverse_)
import           Data.Function                    ((&))
import           Data.Time.Units                  (Second, toMicroseconds)
import           Ledger.Blockchain                (Block)
import           Servant                          (NoContent (NoContent))
import           Servant.Client                   (ClientEnv, runClientM)

import           Cardano.ChainIndex.Types
import qualified Cardano.Node.Client              as NodeClient
import           Ledger.Address                   (Address)
import           Ledger.AddressMap                (AddressMap)
import           Plutus.PAB.Monitoring            (convertLog, handleLogMsgTrace)
import           Wallet.Effects                   (ChainIndexEffect)
import qualified Wallet.Effects                   as WalletEffects
import           Wallet.Emulator.ChainIndex       (ChainIndexControlEffect, ChainIndexEvent)
import qualified Wallet.Emulator.ChainIndex       as ChainIndex
import           Wallet.Emulator.NodeClient       (ChainClientNotification (BlockValidated, SlotChanged))

healthcheck :: Monad m => m NoContent
healthcheck = pure NoContent

processIndexEffects ::
    MonadIO m
    => ChainIndexTrace
    -> MVar AppState
    -> Eff (ChainIndexEffects IO) a
    -> m a
processIndexEffects trace stateVar eff = do
    AppState {_indexState, _indexEvents, _indexFollowerID} <- liftIO $ takeMVar stateVar
    (result, newState) <- liftIO
        $ ChainIndex.handleChainIndexControl eff
        & ChainIndex.handleChainIndex
        & Eff.runState _indexState
        & handleLogMsgTrace (toChainIndexServerMsg trace)
        & runM
    liftIO $ putMVar stateVar AppState{_indexState=newState, _indexEvents=_indexEvents, _indexFollowerID=_indexFollowerID  }
    pure result
        where
            toChainIndexServerMsg :: Trace m ChainIndexServerMsg -> Trace m ChainIndexEvent
            toChainIndexServerMsg = convertLog ChainEvent

startWatching :: (Member ChainIndexEffect effs) => Address -> Eff effs NoContent
startWatching addr = WalletEffects.startWatching addr >> pure NoContent

watchedAddresses :: (Member ChainIndexEffect effs) => Eff effs AddressMap
watchedAddresses = WalletEffects.watchedAddresses

confirmedBlocks :: (Member ChainIndexEffect effs) => Eff effs [Block]
confirmedBlocks = WalletEffects.confirmedBlocks

-- | Update the chain index by asking the node for new blocks since the last
--   time.
syncState ::
    ( Member (State AppState) effs
    , Member (LogMsg ChainIndexServerMsg) effs
    , Member NodeFollowerEffect effs
    , Member ChainIndexControlEffect effs
    )
    => Eff effs ()
syncState = do
    followerID <- use indexFollowerID >>=
        maybe (logInfo ObtainingFollowerID >> newFollower >>= \i -> assign indexFollowerID (Just i) >> return i) pure
    logDebug $ UpdatingChainIndex followerID
    newBlocks <- getBlocks followerID
    logInfo $ ReceivedBlocksTxns (length newBlocks) (length $ fold newBlocks)
    currentSlot <- SlotChanged <$> getSlot
    let notifications = BlockValidated <$> newBlocks
    traverse_ ChainIndex.chainIndexNotify (notifications ++ [currentSlot])

-- | Get the latest transactions from the node and update the index accordingly
updateThread ::
    forall effs.
    ( LastMember IO effs
    , Member (LogMsg ChainIndexServerMsg) effs
    )
    => ChainIndexTrace
    -> Second
    -- ^ Interval between two queries for new blocks
    -> MVar AppState
    -- ^ State of the chain index
    -> ClientEnv
    -- ^ Servant client for the node API
    -> Eff effs ()
updateThread trace updateInterval mv nodeClientEnv = do
    logInfo ObtainingFollowerID
    followerID <-
        liftIO $
        runClientM NodeClient.newFollower nodeClientEnv >>=
        either (error . show) pure
    logInfo $ ObtainedFollowerID followerID
    forever $ do
        watching <- processIndexEffects trace mv WalletEffects.watchedAddresses
        unless (watching == mempty) (fetchNewBlocks trace followerID nodeClientEnv mv)
        liftIO $ threadDelay $ fromIntegral $ toMicroseconds updateInterval

fetchNewBlocks ::
    forall effs.
    ( LastMember IO effs
    , Member (LogMsg ChainIndexServerMsg) effs
    )
    => ChainIndexTrace
    -> FollowerID
    -> ClientEnv
    -> MVar AppState
    -> Eff effs ()
fetchNewBlocks trace followerID nodeClientEnv mv = do
    logInfo AskingNodeForNewBlocks
    newBlocks <-
        liftIO $
        runClientM (NodeClient.getBlocks followerID) nodeClientEnv >>=
        either (error . show) pure
    logInfo (ReceivedBlocksTxns (length newBlocks) (length $ fold newBlocks))
    logInfo AskingNodeForCurrentSlot
    curentSlot <-
        liftIO $
        runClientM NodeClient.getCurrentSlot nodeClientEnv >>=
        either (error . show) pure
    let notifications = BlockValidated <$> newBlocks
    traverse_
        (processIndexEffects trace mv . ChainIndex.chainIndexNotify)
        (notifications ++ [SlotChanged curentSlot])
