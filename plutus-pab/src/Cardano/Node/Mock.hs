{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Cardano.Node.Mock where

import           Control.Concurrent              (threadDelay)
import           Control.Concurrent.MVar         (MVar, modifyMVar_, putMVar, takeMVar)
import           Control.Lens                    (over, set, unto, view)
import           Control.Monad                   (forever, unless, void)
import           Control.Monad.Freer             (Eff, Member, interpret, reinterpret, runM, subsume)
import           Control.Monad.Freer.Extras      (handleZoomedState)
import           Control.Monad.Freer.Log         (LogMessage (..), handleLogWriter, mapLog, renderLogMessages)
import           Control.Monad.Freer.Reader      (Reader)
import qualified Control.Monad.Freer.Reader      as Eff
import           Control.Monad.Freer.State       (State)
import qualified Control.Monad.Freer.State       as Eff
import qualified Control.Monad.Freer.Writer      as Eff
import           Control.Monad.IO.Class          (MonadIO, liftIO)
import           Data.Foldable                   (traverse_)
import           Data.Function                   ((&))
import           Data.List                       (genericDrop)
import           Data.Text                       (Text)
import           Data.Time.Units                 (Second, toMicroseconds)
import           Data.Time.Units.Extra           ()
import           Servant                         (NoContent (NoContent))

import           Cardano.BM.Data.Trace           (Trace)
import           Cardano.Node.Follower           (NodeFollowerEffect)
import           Cardano.Node.RandomTx
import           Cardano.Node.Types
import           Cardano.Protocol.ChainEffect    as CE
import           Cardano.Protocol.FollowerEffect as FE
import qualified Cardano.Protocol.Socket.Client  as Client
import qualified Cardano.Protocol.Socket.Server  as Server
import           Control.Monad.Freer.Extra.Log
import           Ledger                          (Block, Slot (Slot), Tx)
import           Ledger.Tx                       (outputs)
import           Plutus.PAB.Arbitrary            ()
import           Plutus.PAB.Monitoring           (runLogEffects)
import qualified Wallet.Emulator                 as EM
import           Wallet.Emulator.Chain           (ChainControlEffect, ChainEffect, ChainState)
import qualified Wallet.Emulator.Chain           as Chain

healthcheck :: Monad m => m NoContent
healthcheck = pure NoContent

getCurrentSlot :: (Member (State ChainState) effs) => Eff effs Slot
getCurrentSlot = Eff.gets (view EM.currentSlot)

addBlock ::
    ( Member (LogMsg MockServerLogMsg) effs
    , Member ChainControlEffect effs
    )
    => Eff effs ()
addBlock = do
    logInfo $ BlockOperation NewSlot
    void Chain.processBlock

getBlocksSince ::
    ( Member ChainControlEffect effs
    , Member (State ChainState) effs
    )
    => Slot
    -> Eff effs [Block]
getBlocksSince (Slot slotNumber) = do
    void Chain.processBlock
    chainNewestFirst <- Eff.gets (view Chain.chainNewestFirst)
    pure $ genericDrop slotNumber $ reverse chainNewestFirst

consumeEventHistory :: MonadIO m => MVar AppState -> m [LogMessage MockServerLogMsg]
consumeEventHistory stateVar =
    liftIO $ do
        oldState <- takeMVar stateVar
        let events = view eventHistory oldState
        let newState = set eventHistory mempty oldState
        putMVar stateVar newState
        pure events

addTx :: (Member (LogMsg MockServerLogMsg) effs, Member ChainEffect effs) => Tx -> Eff effs NoContent
addTx tx = do
    logInfo $ BlockOperation $ NewTransaction tx
    Chain.queueTx tx
    pure NoContent



type NodeServerEffects m
     = '[ GenRandomTx
        , LogMsg MockServerLogMsg
        , NodeFollowerEffect
        , LogMsg NodeFollowerLogMsg
        , ChainControlEffect
        , ChainEffect
        , State NodeFollowerState
        , State ChainState
        , LogMsg MockServerLogMsg
        , Reader Client.ClientHandler
        , Reader Server.ServerHandler
        , State AppState
        , LogMsg MockServerLogMsg
        , LogMsg Text
        , m]

------------------------------------------------------------


-- | Run all chain effects in the IO Monad
runChainEffects ::
    Server.ServerHandler
 -> Client.ClientHandler
 -> MVar AppState
 -> Eff (NodeServerEffects IO) a
 -> IO ([LogMessage MockServerLogMsg], a)
runChainEffects serverHandler clientHandler stateVar eff = do
    oldAppState <- liftIO $ takeMVar stateVar
    ((a, events), newState) <- liftIO
            $ processBlock eff
            & runRandomTx
            & runNodeFollwer
            & runChain
            & mergeState
            & toWriter
            & runReaders oldAppState
            & interpret renderLogMessages
            & runStderrLog
            & runM
    liftIO $ putMVar stateVar newState
    pure (events, a)
        where
            processBlock e = e >>= \r -> Chain.processBlock >> pure r

            runRandomTx = subsume . runGenRandomTx

            runNodeFollwer = interpret (mapLog FollowerMsg) . FE.handleNodeFollower

            runChain = interpret (mapLog ProcessingChainEvent) . reinterpret CE.handleChain . interpret (mapLog ProcessingChainEvent) . reinterpret Chain.handleControlChain

            mergeState = interpret (handleZoomedState chainState) . interpret (handleZoomedState followerState)

            toWriter = Eff.runWriter . reinterpret (handleLogWriter @MockServerLogMsg @[LogMessage MockServerLogMsg] (unto return))

            runReaders s = Eff.runState s . Eff.runReader serverHandler . Eff.runReader clientHandler

processChainEffects ::
    Trace IO MockServerLogMsg
    -> Server.ServerHandler
    -> Client.ClientHandler
    -> MVar AppState
    -> Eff (NodeServerEffects IO) a
    -> IO a
processChainEffects trace serverHandler clientHandler stateVar eff = do
    (events, result) <- liftIO $ runChainEffects serverHandler clientHandler stateVar eff
    runLogEffects trace $ traverse_ (\(LogMessage _ chainEvent) -> logDebug chainEvent) events
    liftIO $
        modifyMVar_
            stateVar
            (\state -> pure $ over eventHistory (mappend events) state)
    pure result

-- | Calls 'addBlock' at the start of every slot, causing pending transactions
--   to be validated and added to the chain.
slotCoordinator ::
    Trace IO MockServerLogMsg
 ->  Second
 -> Server.ServerHandler
 -> Client.ClientHandler
 -> MVar AppState
 -> IO a
slotCoordinator trace slotLength serverHandler clientHandler stateVar =
    forever $ do
        void $ processChainEffects trace serverHandler clientHandler stateVar addBlock
        liftIO $ threadDelay $ fromIntegral $ toMicroseconds slotLength

-- | Generates a random transaction once in each 'mscRandomTxInterval' of the
--   config
transactionGenerator ::
  Trace IO MockServerLogMsg
 -> Second
 -> Server.ServerHandler
 -> Client.ClientHandler
 -> MVar AppState
 -> IO ()
transactionGenerator trace interval serverHandler clientHandler stateVar =
    forever $ do
        liftIO $ threadDelay $ fromIntegral $ toMicroseconds interval
        processChainEffects trace serverHandler clientHandler stateVar $ do
            tx' <- genRandomTx
            unless (null $ view outputs tx') (void $ addTx tx')

-- | Discards old blocks according to the 'BlockReaperConfig'. (avoids memory
--   leak)
blockReaper ::
  Trace IO MockServerLogMsg
 -> BlockReaperConfig
 -> Server.ServerHandler
 -> Client.ClientHandler
 -> MVar AppState
 -> IO ()
blockReaper tracer BlockReaperConfig {brcInterval, brcBlocksToKeep} serverHandler clientHandler stateVar =
    forever $ do
        void $
            processChainEffects
                tracer
                serverHandler
                clientHandler
                stateVar
                (Eff.modify (over Chain.chainNewestFirst (take brcBlocksToKeep)))
        liftIO $ threadDelay $ fromIntegral $ toMicroseconds brcInterval
