{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Cardano.Protocol.Socket.Mock.Server where

import           Control.Concurrent               (forkIO)
import           Control.Concurrent.MVar          (MVar, newMVar, putMVar, takeMVar)
import           Control.Monad.Freer              (Eff, runM)
import           Control.Monad.Freer.Extra.Log
import           Control.Monad.Freer.State        (State)
import qualified Control.Monad.Freer.State        as Eff
import           Control.Monad.Freer.Writer       (Writer)
import qualified Control.Monad.Freer.Writer       as Eff
import           Control.Monad.IO.Class           (MonadIO, liftIO)
import           Control.Monad.Logger             (MonadLogger, logDebugN, logInfoN, runStdoutLoggingT)
import           Data.Foldable                    (traverse_)
import           Data.Functor                     (void, ($>))
import           Data.Proxy                       (Proxy (..))
import           Data.Text.Prettyprint.Doc        (Pretty (pretty))
import qualified Network.Wai.Handler.Warp         as Warp
import           Servant                          (Application, NoContent (..), hoistServer, serve)

import           Cardano.Protocol                 (addBlock)
import           Cardano.Protocol.Socket.Mock.API
import           Cardano.Protocol.Socket.Server
import           Plutus.SCB.Utils                 (tshow)
import           Wallet.Emulator.Chain

type MockServerEffects m = '[ChainEffect, State ChainState, Writer [ChainEvent], Log, m]

data MockServerConfig =
     MockServerConfig { mscControlPort :: Int
                      , mscSocket      :: String
                      }

runMockServerEffects ::
    (MonadIO m, MonadLogger m)
    => MVar ChainState -> Eff (MockServerEffects IO) a -> m a
runMockServerEffects stateVar eff = do
    oldChainState <- liftIO $ takeMVar stateVar
    ((a, newState), events) <- liftIO
        $ runM
        $ runStderrLog
        $ Eff.runWriter
        $ Eff.runState oldChainState
        $ handleChain eff
    liftIO $ putMVar stateVar newState
    traverse_ (\event -> logDebugN $ "Event: " <> tshow (pretty event)) events
    return a

app :: MVar ChainState -> Application
app stateVar =
    serve (Proxy @API) $
    hoistServer
        (Proxy @API)
        (runStdoutLoggingT . runMockServerEffects stateVar) -- interpreter
        (addBlock $> NoContent)

main :: (MonadIO m, MonadLogger m) => MockServerConfig -> m ()
main (MockServerConfig port sock) = do
    stateVar <- liftIO $ newMVar emptyChainState
    logInfoN "Starting node protocol interface"
    void $ liftIO $ forkIO $
        void $ startServerNode sock stateVar
    logInfoN "Starting control interface."
    liftIO $ Warp.run port $ app stateVar
