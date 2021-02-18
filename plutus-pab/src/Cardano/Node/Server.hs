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
import           Control.Monad.Freer.Extras.Log  (logInfo)
import           Control.Monad.IO.Class          (liftIO)
import           Data.Function                   ((&))
import           Data.Proxy                      (Proxy (Proxy))
import qualified Network.Wai.Handler.Warp        as Warp
import           Servant                         (Application, hoistServer, serve, (:<|>) ((:<|>)))
import           Servant.Client                  (BaseUrl (baseUrlPort))

import           Cardano.BM.Data.Trace           (Trace)
import           Cardano.Node.API                (API)
import           Cardano.Node.Follower           (getBlocks, newFollower)
import           Cardano.Node.Mock
import           Cardano.Node.RandomTx           (genRandomTx)
import           Cardano.Node.Types
import qualified Cardano.Protocol.Socket.Client  as Client
import qualified Cardano.Protocol.Socket.Server  as Server
import           Plutus.PAB.Arbitrary            ()
import           Plutus.PAB.Monitoring           (runLogEffects)

app ::
 Trace IO MockServerLogMsg
 -> Server.ServerHandler
 -> Client.ClientHandler
 -> MVar AppState
 -> Application
app trace serverHandler clientHandler stateVar =
    serve (Proxy @API) $
    hoistServer
        (Proxy @API)
        (liftIO . processChainEffects trace serverHandler clientHandler stateVar)
        (healthcheck :<|> addTx :<|> getCurrentSlot :<|>
         (genRandomTx :<|>
          consumeEventHistory stateVar) :<|>
          (newFollower :<|> getBlocks))

data Ctx = Ctx { serverHandler :: Server.ServerHandler
               , clientHandler :: Client.ClientHandler
               , serverState   :: MVar AppState
               , mockTrace     :: Trace IO MockServerLogMsg
               }

main :: Trace IO MockServerLogMsg -> MockServerConfig -> Availability -> IO ()
main trace MockServerConfig { mscBaseUrl
                            , mscRandomTxInterval
                            , mscBlockReaper
                            , mscSlotLength
                            , mscInitialTxWallets
                            , mscSocketPath} availability = runLogEffects trace $ do

    serverHandler <- liftIO $ Server.runServerNode mscSocketPath (_chainState $ initialAppState mscInitialTxWallets)
    clientHandler <- liftIO $ Client.runClientNode mscSocketPath
    clientState <- liftIO $ newMVar (initialAppState mscInitialTxWallets)
    serverState <- liftIO $ newMVar (initialAppState mscInitialTxWallets)

    let ctx = Ctx serverHandler clientHandler serverState trace

    runSlotCoordinator ctx mscSlotLength
    maybe (logInfo NoRandomTxGeneration) (runRandomTxGeneration ctx) mscRandomTxInterval
    maybe (logInfo KeepingOldBlocks) (runBlockReaper ctx) mscBlockReaper

    logInfo $ StartingMockServer $ baseUrlPort mscBaseUrl
    liftIO $ Warp.runSettings warpSettings $ app trace serverHandler clientHandler clientState

        where
            warpSettings = Warp.defaultSettings & Warp.setPort (baseUrlPort mscBaseUrl) & Warp.setBeforeMainLoop (available availability)

            runRandomTxGeneration Ctx { serverHandler , clientHandler , serverState , mockTrace } randomTxInterval = do
                    logInfo StartingRandomTx
                    void $ liftIO $ forkIO $ transactionGenerator mockTrace randomTxInterval serverHandler clientHandler serverState

            runBlockReaper Ctx { serverHandler , clientHandler , serverState , mockTrace } reaperConfig = do
                logInfo RemovingOldBlocks
                void $ liftIO $ forkIO $ blockReaper mockTrace reaperConfig serverHandler clientHandler serverState

            runSlotCoordinator Ctx { serverHandler , clientHandler , serverState , mockTrace } slotLength = do
                logInfo StartingSlotCoordination
                void $ liftIO $ forkIO $ slotCoordinator mockTrace slotLength serverHandler clientHandler serverState
