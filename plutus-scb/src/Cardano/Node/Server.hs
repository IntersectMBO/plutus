{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Cardano.Node.Server
    ( main
    , MockServerConfig(..)
    ) where

import           Control.Concurrent              (MVar, forkIO, newMVar)
import           Control.Concurrent.Availability (Availability, available)
import           Control.Concurrent.STM
import           Control.Monad                   (void)
import           Control.Monad.IO.Class          (MonadIO, liftIO)
import           Control.Monad.Logger            (logInfoN, runStdoutLoggingT)
import           Data.Function                   ((&))
import           Data.Proxy                      (Proxy (Proxy))
import qualified Network.Wai.Handler.Warp        as Warp
import           Servant                         ((:<|>) ((:<|>)), Application, hoistServer, serve)
import           Servant.Client                  (BaseUrl (baseUrlPort))

import           Cardano.Node.API                (API)
import           Cardano.Node.Follower           (getBlocks, newFollower)
import           Cardano.Node.Mock
import           Cardano.Node.RandomTx           (genRandomTx)
import           Cardano.Node.Types
import           Ledger                          (Block, Tx (..))

import           Plutus.SCB.Arbitrary            ()
import           Plutus.SCB.Utils                (tshow)

app :: TQueue Tx -> TQueue Block -> MVar AppState -> Application
app txQueue blockQueue stateVar =
    serve (Proxy @API) $
    hoistServer
        (Proxy @API)
        (runStdoutLoggingT . processChainEffects txQueue blockQueue stateVar)
        (healthcheck :<|> addTx :<|> getCurrentSlot :<|>
         (genRandomTx :<|>
          consumeEventHistory stateVar) :<|>
          (newFollower :<|> getBlocks)
          )

main :: MonadIO m => MockServerConfig -> Availability -> m ()
main MockServerConfig { mscBaseUrl
                      , mscRandomTxInterval
                      , mscBlockReaper
                      , mscSlotLength
                      , mscInitialTxWallets
                      } availability =
    runStdoutLoggingT $ do
        blockQueue <- liftIO newTQueueIO
        txQueue    <- liftIO newTQueueIO
        -- Local chain state (node client)
        clientStateVar <- liftIO $ newMVar (initialAppState mscInitialTxWallets)
        -- Global chain state (node server)
        serverStateVar <- liftIO $ newMVar (initialAppState mscInitialTxWallets)

        logInfoN "Starting slot coordination thread."
        void $
            liftIO $
            forkIO $ runStdoutLoggingT $ slotCoordinator mscSlotLength txQueue blockQueue serverStateVar
        case mscRandomTxInterval of
            Nothing -> logInfoN "No random transactions will be generated."
            Just i -> do
                logInfoN "Starting transaction generator thread."
                void $
                    liftIO $
                    forkIO $ runStdoutLoggingT $ transactionGenerator i txQueue blockQueue serverStateVar
        case mscBlockReaper of
            Nothing -> logInfoN "Old blocks will be kept in memory forever"
            Just cfg -> do
                logInfoN "Starting block reaper thread."
                void $
                    liftIO $
                    forkIO $ runStdoutLoggingT $ blockReaper cfg txQueue blockQueue serverStateVar
        let mscPort = baseUrlPort mscBaseUrl
        let warpSettings :: Warp.Settings
            warpSettings = Warp.defaultSettings & Warp.setPort mscPort & Warp.setBeforeMainLoop (available availability)
        logInfoN $ "Starting mock node server on port: " <> tshow mscPort
        liftIO $ Warp.runSettings warpSettings $ app txQueue blockQueue clientStateVar
