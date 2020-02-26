{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Cardano.Node.Server
    ( main
    , MockServerConfig(..)
    ) where

import           Control.Concurrent       (forkIO)
import           Control.Concurrent.MVar  (MVar, newMVar)
import           Control.Monad            (void)
import           Control.Monad.IO.Class   (MonadIO, liftIO)
import           Control.Monad.Logger     (MonadLogger, logInfoN, runStdoutLoggingT)
import           Data.Proxy               (Proxy (Proxy))
import qualified Network.Wai.Handler.Warp as Warp
import           Servant                  ((:<|>) ((:<|>)), Application, hoistServer, serve)
import           Servant.Client           (BaseUrl (baseUrlPort))

import           Cardano.Node.API         (API)
import           Cardano.Node.Mock
import           Cardano.Node.RandomTx    (genRandomTx)
import           Cardano.Node.Types

import           Plutus.SCB.Arbitrary     ()
import           Plutus.SCB.Utils         (tshow)

app :: MVar AppState -> Application
app stateVar =
    serve (Proxy @API) $
    hoistServer
        (Proxy @API)
        (runStdoutLoggingT . processChainEffects stateVar)
        (healthcheck :<|> addTx :<|> getCurrentSlot :<|>
         (genRandomTx :<|> utxoAt :<|> blockchain :<|>
          consumeEventHistory stateVar))

main :: (MonadIO m, MonadLogger m) => MockServerConfig -> m ()
main MockServerConfig { mscBaseUrl
                      , mscRandomTxInterval
                      , mscBlockReaper
                      , mscSlotLength
                      } = do
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
                liftIO $ forkIO $ runStdoutLoggingT $ blockReaper cfg stateVar
    let mscPort = baseUrlPort mscBaseUrl
    logInfoN $ "Starting mock node server on port: " <> tshow mscPort
    liftIO $ Warp.run mscPort $ app stateVar
