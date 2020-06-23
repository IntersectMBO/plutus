{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module Cardano.Node.Mock where

import           Control.Concurrent            (threadDelay)
import           Control.Concurrent.MVar       (MVar, modifyMVar_, putMVar, takeMVar)
import           Control.Lens                  (over, set, view)
import           Control.Monad                 (forever, void, when)
import           Control.Monad.Freer           (Eff, Member, interpret, runM)
import           Control.Monad.Freer.Extras    (handleZoomedState)
import           Control.Monad.Freer.State     (State)
import qualified Control.Monad.Freer.State     as Eff
import           Control.Monad.Freer.Writer    (Writer)
import qualified Control.Monad.Freer.Writer    as Eff
import           Control.Monad.IO.Class        (MonadIO, liftIO)
import           Control.Monad.Logger          (MonadLogger, logDebugN)
import           Data.Foldable                 (traverse_)
import           Data.List                     (genericDrop)
import           Data.Text.Prettyprint.Doc     (Pretty (pretty))
import           Data.Time.Units               (Second, toMicroseconds)
import           Data.Time.Units.Extra         ()
import           Servant                       (NoContent (NoContent))

import           Ledger                        (Block, Slot (Slot), Tx)
import qualified Ledger
import           Ledger.Tx                     (outputs)

import           Cardano.Node.Follower         (NodeFollowerEffect, handleNodeFollower)
import           Cardano.Node.RandomTx
import           Cardano.Node.Types            as T
import           Control.Monad.Freer.Extra.Log

import           Plutus.SCB.Arbitrary          ()
import           Plutus.SCB.Utils              (tshow)

import qualified Wallet.Emulator               as EM
import           Wallet.Emulator.Chain         (ChainEffect, ChainEvent, ChainState)
import qualified Wallet.Emulator.Chain         as Chain

healthcheck :: Monad m => m NoContent
healthcheck = pure NoContent

getCurrentSlot :: (Member (State ChainState) effs) => Eff effs Slot
getCurrentSlot = Eff.gets (view EM.currentSlot)

addBlock ::
    ( Member Log effs
    , Member ChainEffect effs
    )
    => Eff effs ()
addBlock = do
    logInfo "Adding slot"
    void Chain.processBlock

getBlocksSince ::
    ( Member ChainEffect effs
    , Member (State ChainState) effs
    )
    => Slot
    -> Eff effs [Block]
getBlocksSince (Slot slotNumber) = do
    void Chain.processBlock
    chainNewestFirst <- Eff.gets (view EM.chainNewestFirst)
    pure $ genericDrop slotNumber $ reverse chainNewestFirst

consumeEventHistory :: MonadIO m => MVar AppState -> m [ChainEvent]
consumeEventHistory stateVar =
    liftIO $ do
        oldState <- takeMVar stateVar
        let events = view eventHistory oldState
        let newState = set eventHistory mempty oldState
        putMVar stateVar newState
        pure events

addTx :: (Member Log effs, Member ChainEffect effs) => Tx -> Eff effs NoContent
addTx tx = do
    logInfo $ "Adding tx " <> tshow (Ledger.txId tx)
    logDebug $ tshow (pretty tx)
    Chain.queueTx tx
    pure NoContent

type NodeServerEffects m
     = '[ GenRandomTx, NodeFollowerEffect, ChainEffect, State NodeFollowerState, State ChainState, Writer [ChainEvent], State AppState, Log, m]

------------------------------------------------------------
runChainEffects ::
       MVar AppState -> Eff (NodeServerEffects IO) a -> IO ([ChainEvent], a)
runChainEffects stateVar eff = do
    oldAppState <- liftIO $ takeMVar stateVar
    ((a, events), newState) <- liftIO
        $ runM
        $ runStderrLog
        $ Eff.runState oldAppState
        $ Eff.runWriter
        $ interpret (handleZoomedState T.chainState)
        $ interpret (handleZoomedState T.followerState)
        $ Chain.handleChain
        $ handleNodeFollower
        $ runGenRandomTx
        $ do result <- eff
             void Chain.processBlock
             pure result
    liftIO $ putMVar stateVar newState
    pure (events, a)

processChainEffects ::
       (MonadIO m, MonadLogger m)
    => MVar AppState
    -> Eff (NodeServerEffects IO) a
    -> m a
processChainEffects stateVar eff = do
    (events, result) <- liftIO $ runChainEffects stateVar eff
    traverse_ (\event -> logDebugN $ "Event: " <> tshow (pretty event)) events
    liftIO $
        modifyMVar_
            stateVar
            (\state -> pure $ over eventHistory (mappend events) state)
    pure result

-- | Calls 'addBlock' at the start of every slot, causing pending transactions
--   to be validated and added to the chain.
slotCoordinator :: (MonadIO m, MonadLogger m) => Second -> MVar AppState -> m ()
slotCoordinator slotLength stateVar =
    forever $ do
        void $ processChainEffects stateVar addBlock
        liftIO $ threadDelay $ fromIntegral $ toMicroseconds slotLength

-- | Generates a random transaction once in each 'mscRandomTxInterval' of the
--   config
transactionGenerator ::
       (MonadIO m, MonadLogger m) => Second -> MVar AppState -> m ()
transactionGenerator itvl stateVar =
    forever $ do
        liftIO $ threadDelay $ fromIntegral $ toMicroseconds itvl
        processChainEffects stateVar $ do
            tx' <- genRandomTx
            when (not . null $ view outputs tx') (void $ addTx tx')

-- | Discards old blocks according to the 'BlockReaperConfig'. (avoids memory
--   leak)
blockReaper ::
       (MonadIO m, MonadLogger m) => BlockReaperConfig -> MVar AppState -> m ()
blockReaper BlockReaperConfig {brcInterval, brcBlocksToKeep} stateVar =
    forever $ do
        void $
            processChainEffects
                stateVar
                (Eff.modify (over EM.chainNewestFirst (take brcBlocksToKeep)))
        liftIO $ threadDelay $ fromIntegral $ toMicroseconds brcInterval
