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

import           Plutus.SCB.Arbitrary            ()
import           Plutus.SCB.Utils                (tshow)

app :: MVar AppState -> Application
app stateVar =
    serve (Proxy @API) $
    hoistServer
        (Proxy @API)
        (runStdoutLoggingT . processChainEffects stateVar)
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
                      } availability =
    runStdoutLoggingT $ do
        stateVar <- liftIO $ newMVar initialAppState
        logInfoN "Starting slot coordination thread."
        void $
            liftIO $
            forkIO $ runStdoutLoggingT $ slotCoordinator mscSlotLength stateVar
        case mscRandomTxInterval of
            Nothing -> logInfoN "No random transactions will be generated."
            Just i -> do
                logInfoN "Starting transaction generator thread."
                void $
                    liftIO $
                    forkIO $ runStdoutLoggingT $ transactionGenerator i stateVar
        case mscBlockReaper of
            Nothing -> logInfoN "Old blocks will be kept in memory forever"
            Just cfg -> do
                logInfoN "Starting block reaper thread."
                void $
                    liftIO $
                    forkIO $ runStdoutLoggingT $ blockReaper cfg stateVar
        let mscPort = baseUrlPort mscBaseUrl
        let warpSettings :: Warp.Settings
            warpSettings = Warp.defaultSettings & Warp.setPort mscPort & Warp.setBeforeMainLoop (available availability)
        logInfoN $ "Starting mock node server on port: " <> tshow mscPort
        liftIO $ Warp.runSettings warpSettings $ app stateVar
