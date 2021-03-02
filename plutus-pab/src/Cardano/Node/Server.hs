{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Cardano.Node.Server
    ( main
    ) where

import           Control.Concurrent               (MVar, forkIO, newMVar)
import           Control.Concurrent.Availability  (Availability, available)
import           Control.Monad                    (void)
import           Control.Monad.Freer.Extras.Log   (logInfo)
import           Control.Monad.IO.Class           (liftIO)
import           Data.Function                    ((&))
import           Data.Proxy                       (Proxy (Proxy))
import qualified Network.Wai.Handler.Warp         as Warp
import           Servant                          (Application, hoistServer, serve, (:<|>) ((:<|>)))
import           Servant.Client                   (BaseUrl (baseUrlPort))

import           Cardano.BM.Data.Trace            (Trace)
import           Cardano.Node.API                 (API)
import           Cardano.Node.Mock
import           Cardano.Node.Types
import qualified Cardano.Protocol.Socket.Server   as Server
import           Plutus.PAB.Arbitrary             ()
import qualified Plutus.PAB.Monitoring.Monitoring as LM

app ::
    Trace IO MockServerLogMsg
 -> Server.ServerHandler
 -> MVar AppState
 -> Application
app trace serverHandler stateVar =
    serve (Proxy @API) $
    hoistServer
        (Proxy @API)
        (liftIO . processChainEffects trace serverHandler stateVar)
        (healthcheck :<|> getCurrentSlot :<|>
         (genRandomTx :<|>
          consumeEventHistory stateVar))

data Ctx = Ctx { serverHandler :: Server.ServerHandler
               , serverState   :: MVar AppState
               , mockTrace     :: Trace IO MockServerLogMsg
               }

main :: Trace IO MockServerLogMsg -> MockServerConfig -> Availability -> IO ()
main trace MockServerConfig { mscBaseUrl
                            , mscRandomTxInterval
                            , mscBlockReaper
                            , mscSlotLength
                            , mscInitialTxWallets
                            , mscSocketPath} availability = LM.runLogEffects trace $ do

    serverHandler <- liftIO $ Server.runServerNode mscSocketPath (_chainState $ initialAppState mscInitialTxWallets)
    serverState <- liftIO $ newMVar (initialAppState mscInitialTxWallets)

    let ctx = Ctx serverHandler serverState trace

    runSlotCoordinator ctx mscSlotLength
    maybe (logInfo NoRandomTxGeneration) (runRandomTxGeneration ctx) mscRandomTxInterval
    maybe (logInfo KeepingOldBlocks) (runBlockReaper ctx) mscBlockReaper

    logInfo $ StartingMockServer $ baseUrlPort mscBaseUrl
    liftIO $ Warp.runSettings warpSettings $ app trace serverHandler serverState

        where
            warpSettings = Warp.defaultSettings & Warp.setPort (baseUrlPort mscBaseUrl) & Warp.setBeforeMainLoop (available availability)

            runRandomTxGeneration Ctx { serverHandler , serverState , mockTrace } randomTxInterval = do
                    logInfo StartingRandomTx
                    void $ liftIO $ forkIO $ transactionGenerator mockTrace randomTxInterval serverHandler serverState

            runBlockReaper Ctx { serverHandler , serverState , mockTrace } reaperConfig = do
                logInfo RemovingOldBlocks
                void $ liftIO $ forkIO $ blockReaper mockTrace reaperConfig serverHandler serverState

            runSlotCoordinator Ctx { serverHandler , serverState , mockTrace } slotLength = do
                logInfo StartingSlotCoordination
                void $ liftIO $ forkIO $ slotCoordinator mockTrace slotLength serverHandler serverState
