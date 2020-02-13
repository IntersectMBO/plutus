{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Cardano.Node.MockServer(
    MockServerConfig(..)
    , defaultConfig
    , main
    ) where

import           Cardano.Node.API               (API)
import           Control.Concurrent             (forkIO, threadDelay)
import           Control.Concurrent.MVar        (MVar, newMVar, putMVar, takeMVar)
import           Control.Lens                   (view, over)
import           Control.Monad                  (forever, void)
import           Control.Monad.Freer            (Eff, Member)
import           Control.Monad.Freer.State      (State)
import qualified Control.Monad.Freer.State      as Eff
import           Control.Monad.Freer.Writer     (Writer)
import qualified Control.Monad.Freer.Writer     as Eff
import           Control.Monad.IO.Class         (MonadIO, liftIO)
import           Control.Monad.Logger           (MonadLogger, logDebugN, logInfoN, runStdoutLoggingT)
import           Data.Foldable                  (traverse_)
import qualified Data.Map                       as Map
import           Data.Proxy                     (Proxy (Proxy))
import           Data.Text.Prettyprint.Doc      (Pretty (pretty))
import           Data.Time.Units                (Second, toMicroseconds)

import qualified Network.Wai.Handler.Warp       as Warp
import           Servant                        ((:<|>) ((:<|>)), Application, NoContent (NoContent), hoistServer,
                                                 serve)

import           Language.Plutus.Contract.Trace (InitialDistribution)
import qualified Language.Plutus.Contract.Trace as Trace

import           Ledger                         (Slot, Tx)
import qualified Ledger
import qualified Ledger.Blockchain              as Blockchain

import           Cardano.Node.RandomTx
import           Cardano.Node.SimpleLog

import           Plutus.SCB.Arbitrary           ()
import           Plutus.SCB.Utils               (tshow)

import qualified Wallet.Emulator                as EM
import           Wallet.Emulator.Chain          (ChainEffect, ChainEvent, ChainState)
import qualified Wallet.Emulator.Chain          as Chain
import qualified Wallet.Emulator.MultiAgent     as MultiAgent

data BlockReaperConfig =
    BlockReaperConfig
        { brcInterval :: Second
        , brcBlocksToKeep :: Int
        }

data MockServerConfig =
    MockServerConfig
        { mscPort                :: Int
        , mscSlotLength          :: Second
        -- ^ Duration of one slot
        , mscRandomTxInterval    :: Maybe Second
        -- ^ Time between two randomly generated transactions
        , mscInitialDistribution :: InitialDistribution
        -- ^ Initial distribution of funds to wallets
        , mscBlockReaper         :: Maybe BlockReaperConfig
        -- ^ When to discard old blocks
        }

defaultConfig :: MockServerConfig
defaultConfig =
    MockServerConfig
        { mscPort = 8082
        , mscSlotLength = 5
        , mscRandomTxInterval = Just 20
        , mscInitialDistribution = Trace.defaultDist
        , mscBlockReaper = Just BlockReaperConfig{brcInterval = 600, brcBlocksToKeep = 100 }
        }

healthcheck :: Monad m => m NoContent
healthcheck = pure NoContent

getCurrentSlot :: (Member (State ChainState) effs) => Eff effs Slot
getCurrentSlot = Eff.gets (Blockchain.lastSlot . view EM.chainNewestFirst)

addBlock :: (Member SimpleLog effs, Member ChainEffect effs) => Eff effs ()
addBlock = do
    simpleLogInfo "Adding slot"
    void Chain.processBlock

addTx :: (Member SimpleLog effs, Member ChainEffect effs) => Tx -> Eff effs NoContent
addTx tx = do
    simpleLogInfo  $ "Adding tx " <> tshow (Ledger.txId tx)
    simpleLogDebug $ tshow (pretty tx)
    Chain.queueTx tx
    pure NoContent

type NodeServerEffects m = [GenRandomTx, ChainEffect, State ChainState, Writer [ChainEvent], SimpleLog, m]

------------------------------------------------------------

runChainEffects ::
        ( MonadIO m, MonadLogger m )
        => MVar ChainState
        -> Eff (NodeServerEffects m) a
        -> m ([ChainEvent], a)
runChainEffects stateVar eff = do
    oldState <- liftIO $ takeMVar stateVar
    ((a, newState), events) <- runSimpleLog
        $ Eff.runWriter
        $ Eff.runState oldState
        $ Chain.handleChain
        $ runGenRandomTx eff
    liftIO $ putMVar stateVar newState
    pure (events, a)

processChainEffects ::
    ( MonadIO m, MonadLogger m )
    => MVar ChainState
    -> Eff (NodeServerEffects m) a
    -> m a
processChainEffects stateVar eff = do
    (events, result) <- runChainEffects stateVar eff
    -- TODO: We need to process the events instead of just printing them out
    -- Process = add them to some internal queue that the clients can consume
    traverse_ (logDebugN . tshow . pretty) events
    pure result

-- | Calls 'addBlock' at the start of every slot, causing pending transactions
--   to be validated and added to the chain.
slotCoordinator ::
    ( MonadIO m
    , MonadLogger m
    )
    => Second
    -> MVar ChainState
    -> m ()
slotCoordinator slotLength  stateVar =
    forever $ do
        void $ processChainEffects stateVar addBlock
        liftIO $ threadDelay $ fromIntegral $ toMicroseconds slotLength

-- | Generates a random transaction once in each 'mscRandomTxInterval' of the 
--   config
transactionGenerator ::
    ( MonadIO m
    , MonadLogger m
    )
    => Second
    -> MVar ChainState
    -> m ()
transactionGenerator itvl stateVar =
    forever $ do
        void $ processChainEffects stateVar (genRandomTx >>= addTx)
        liftIO $ threadDelay $ fromIntegral $ toMicroseconds itvl

-- | Discards old blocks according to the 'BlockReaperConfig'. (avoids memory 
--   leak)
blockReaper ::
    ( MonadIO m
    , MonadLogger m
    )
    => BlockReaperConfig
    -> MVar ChainState
    -> m ()
blockReaper BlockReaperConfig{brcInterval, brcBlocksToKeep} stateVar =
    forever $ do
        void $ processChainEffects stateVar (Eff.modify (over EM.chainNewestFirst (take brcBlocksToKeep)))
        liftIO $ threadDelay $ fromIntegral $ toMicroseconds brcInterval

app :: MVar ChainState -> Application
app stateVar =
    serve (Proxy @API) $
    hoistServer
        (Proxy @API)
        (runStdoutLoggingT . processChainEffects stateVar)
        (healthcheck
        :<|> addTx
        :<|> getCurrentSlot
        :<|> genRandomTx)

main :: (MonadIO m, MonadLogger m) => MockServerConfig -> m ()
main config = do
    let MockServerConfig{mscPort, mscInitialDistribution, mscRandomTxInterval, mscBlockReaper, mscSlotLength} = config
    stateVar <- liftIO $ newMVar (initialChainState mscInitialDistribution)
    logInfoN "Starting slot coordination thread."
    void $ liftIO $ forkIO $ runStdoutLoggingT $ slotCoordinator mscSlotLength stateVar
    case mscRandomTxInterval of
        Nothing -> logInfoN "No random transactions will be generated."
        Just i -> do
            logInfoN "Starting transaction generator thread."
            void $ liftIO $ forkIO $ runStdoutLoggingT $ transactionGenerator i stateVar
    case mscBlockReaper of
        Nothing -> logInfoN "Old blocks will be kept in memory forever"
        Just cfg -> do
            logInfoN "Starting block reaper thread."
            void $ liftIO $ forkIO $ runStdoutLoggingT $ blockReaper cfg stateVar
    logInfoN $ "Starting mock node server on port: " <> tshow mscPort
    liftIO $ Warp.run mscPort $ app stateVar

initialChainState :: InitialDistribution -> ChainState
initialChainState =
    view EM.chainState
    . MultiAgent.emulatorStateInitialDist
    . Map.mapKeys EM.walletPubKey
