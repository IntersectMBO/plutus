{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Cardano.Node.Mock where

import           Control.Concurrent              (threadDelay)
import           Control.Concurrent.MVar         (MVar, modifyMVar_, putMVar, takeMVar)
import           Control.Lens                    (over, set, unto, view)
import           Control.Monad                   (forever, unless, void)
import           Control.Monad.Freer             (Eff, Member, interpret, reinterpret, runM)
import           Control.Monad.Freer.Extras      (handleZoomedState)
import           Control.Monad.Freer.Log         (LogMessage, handleLogWriter, mapLog, renderLogMessages)
import           Control.Monad.Freer.Reader      (Reader)
import qualified Control.Monad.Freer.Reader      as Eff
import           Control.Monad.Freer.State       (State)
import qualified Control.Monad.Freer.State       as Eff
import qualified Control.Monad.Freer.Writer      as Eff
import           Control.Monad.IO.Class          (MonadIO, liftIO)
import           Control.Monad.Logger            (MonadLogger, logDebugN)
import           Data.Foldable                   (traverse_)
import           Data.List                       (genericDrop)
import           Data.Text                       (Text)
import           Data.Text.Prettyprint.Doc       (Pretty (pretty), (<+>))
import           Data.Time.Units                 (Second, toMicroseconds)
import           Data.Time.Units.Extra           ()
import           Servant                         (NoContent (NoContent))

import           Ledger                          (Block, Slot (Slot), Tx)

import qualified Ledger
import           Ledger.Tx                       (outputs)

import           Cardano.Node.Follower           (NodeFollowerEffect, NodeFollowerLogMsg)
import           Cardano.Node.RandomTx
import           Cardano.Node.Types              as T
import           Cardano.Protocol.ChainEffect    as CE
import           Cardano.Protocol.FollowerEffect as FE
import qualified Cardano.Protocol.Socket.Client  as Client
import qualified Cardano.Protocol.Socket.Server  as Server
import           Control.Monad.Freer.Extra.Log

import           Plutus.SCB.Arbitrary            ()
import           Plutus.SCB.Utils                (tshow)

import qualified Wallet.Emulator                 as EM
import           Wallet.Emulator.Chain           (ChainControlEffect, ChainEffect, ChainEvent, ChainState)
import qualified Wallet.Emulator.Chain           as Chain

healthcheck :: Monad m => m NoContent
healthcheck = pure NoContent

getCurrentSlot :: (Member (State ChainState) effs) => Eff effs Slot
getCurrentSlot = Eff.gets (view EM.currentSlot)

data MockNodeLogMsg =
        AddingSlot
        | AddingTx Tx

instance Pretty MockNodeLogMsg where
    pretty AddingSlot   = "Adding slot"
    pretty (AddingTx t) = "AddingTx" <+> pretty (Ledger.txId t)

addBlock ::
    ( Member (LogMsg MockNodeLogMsg) effs
    , Member ChainControlEffect effs
    )
    => Eff effs ()
addBlock = do
    logInfo AddingSlot
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

consumeEventHistory :: MonadIO m => MVar AppState -> m [LogMessage ChainEvent]
consumeEventHistory stateVar =
    liftIO $ do
        oldState <- takeMVar stateVar
        let events = view eventHistory oldState
        let newState = set eventHistory mempty oldState
        putMVar stateVar newState
        pure events

addTx :: (Member (LogMsg MockNodeLogMsg) effs, Member ChainEffect effs) => Tx -> Eff effs NoContent
addTx tx = do
    logInfo $ AddingTx tx
    Chain.queueTx tx
    pure NoContent

data NodeServerMsg =
    NodeServerFollowerMsg NodeFollowerLogMsg
    | NodeGenRandomTxMsg GenRandomTxMsg
    | NodeMockNodeMsg MockNodeLogMsg

instance Pretty NodeServerMsg where
    pretty = \case
        NodeServerFollowerMsg m -> pretty m
        NodeGenRandomTxMsg m    -> pretty m
        NodeMockNodeMsg m       -> pretty m

type NodeServerEffects m
     = '[ GenRandomTx
        , LogMsg GenRandomTxMsg
        , NodeFollowerEffect
        , LogMsg NodeFollowerLogMsg
        , ChainControlEffect
        , ChainEffect
        , State NodeFollowerState
        , State ChainState
        , LogMsg ChainEvent
        , Reader Client.ClientHandler
        , Reader Server.ServerHandler
        , State AppState
        , LogMsg MockNodeLogMsg
        , LogMsg NodeServerMsg
        , LogMsg Text
        , m]

------------------------------------------------------------
runChainEffects ::
    Server.ServerHandler
 -> Client.ClientHandler
 -> MVar AppState
 -> Eff (NodeServerEffects IO) a
 -> IO ([LogMessage ChainEvent], a)
runChainEffects serverHandler clientHandler stateVar eff = do
    oldAppState <- liftIO $ takeMVar stateVar
    ((a, events), newState) <- liftIO
        $ runM
        $ runStderrLog
        $ interpret renderLogMessages
        $ interpret (mapLog NodeMockNodeMsg)
        $ Eff.runState oldAppState
        $ Eff.runReader serverHandler
        $ Eff.runReader clientHandler
        $ Eff.runWriter
        $ reinterpret (handleLogWriter @ChainEvent @[LogMessage ChainEvent] (unto return))
        $ interpret (handleZoomedState T.chainState)
        $ interpret (handleZoomedState T.followerState)
        $ CE.handleChain
        $ interpret Chain.handleControlChain
        $ interpret (mapLog NodeServerFollowerMsg)
        $ FE.handleNodeFollower
        $ interpret (mapLog NodeGenRandomTxMsg)
        $ runGenRandomTx
        $ do result <- eff
             void Chain.processBlock
             pure result
    liftIO $ putMVar stateVar newState
    pure (events, a)

processChainEffects ::
       (MonadIO m, MonadLogger m)
    => Server.ServerHandler
    -> Client.ClientHandler
    -> MVar AppState
    -> Eff (NodeServerEffects IO) a
    -> m a
processChainEffects serverHandler clientHandler stateVar eff = do
    (events, result) <- liftIO $ runChainEffects serverHandler clientHandler stateVar eff
    traverse_ (\event -> logDebugN $ "Event: " <> tshow (pretty event)) events
    liftIO $
        modifyMVar_
            stateVar
            (\state -> pure $ over eventHistory (mappend events) state)
    pure result

-- | Calls 'addBlock' at the start of every slot, causing pending transactions
--   to be validated and added to the chain.
slotCoordinator ::
    (MonadIO m, MonadLogger m)
 => Second
 -> Server.ServerHandler
 -> Client.ClientHandler
 -> MVar AppState
 -> m ()
slotCoordinator slotLength serverHandler clientHandler stateVar =
    forever $ do
        void $ processChainEffects serverHandler clientHandler stateVar addBlock
        liftIO $ threadDelay $ fromIntegral $ toMicroseconds slotLength

-- | Generates a random transaction once in each 'mscRandomTxInterval' of the
--   config
transactionGenerator ::
    (MonadIO m, MonadLogger m)
 => Second
 -> Server.ServerHandler
 -> Client.ClientHandler
 -> MVar AppState
 -> m ()
transactionGenerator itvl serverHandler clientHandler stateVar =
    forever $ do
        liftIO $ threadDelay $ fromIntegral $ toMicroseconds itvl
        processChainEffects serverHandler clientHandler stateVar $ do
            tx' <- genRandomTx
            unless (null $ view outputs tx') (void $ addTx tx')

-- | Discards old blocks according to the 'BlockReaperConfig'. (avoids memory
--   leak)
blockReaper ::
    (MonadIO m, MonadLogger m)
 => BlockReaperConfig
 -> Server.ServerHandler
 -> Client.ClientHandler
 -> MVar AppState
 -> m ()
blockReaper BlockReaperConfig {brcInterval, brcBlocksToKeep} serverHandler clientHandler stateVar =
    forever $ do
        void $
            processChainEffects
                serverHandler
                clientHandler
                stateVar
                (Eff.modify (over Chain.chainNewestFirst (take brcBlocksToKeep)))
        liftIO $ threadDelay $ fromIntegral $ toMicroseconds brcInterval
