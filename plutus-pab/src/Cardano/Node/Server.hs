{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TypeApplications   #-}

module Cardano.Node.Server
    ( main
    ) where

import           Cardano.BM.Data.Trace            (Trace)
import           Cardano.Node.API                 (API)
import           Cardano.Node.Mock
import           Cardano.Node.Types
import qualified Cardano.Protocol.Socket.Client   as Client
import qualified Cardano.Protocol.Socket.Server   as Server
import           Control.Concurrent               (MVar, forkIO, modifyMVar_, newMVar)
import           Control.Concurrent.Availability  (Availability, available)
import           Control.Lens                     (over, set)
import           Control.Monad                    (void)
import           Control.Monad.Freer.Delay        (delayThread, handleDelayEffect)
import           Control.Monad.Freer.Extras.Log   (logInfo)
import           Control.Monad.IO.Class           (liftIO)
import           Data.Function                    ((&))
import qualified Data.Map.Strict                  as Map
import           Data.Proxy                       (Proxy (Proxy))
import           Data.Time.Units                  (Second)
import           Ledger                           (Block, Slot (..))
import qualified Ledger.Ada                       as Ada
import qualified Network.Wai.Handler.Warp         as Warp
import           Plutus.PAB.Arbitrary             ()
import qualified Plutus.PAB.Monitoring.Monitoring as LM
import           Servant                          (Application, hoistServer, serve, (:<|>) ((:<|>)))
import           Servant.Client                   (BaseUrl (baseUrlPort))
import           Wallet.Emulator.Chain            (chainNewestFirst, currentSlot)

app ::
    Trace IO MockServerLogMsg
 -> Client.ClientHandler
 -> MVar AppState
 -> Application
app trace clientHandler stateVar =
    serve (Proxy @API) $
    hoistServer
        (Proxy @API)
        (liftIO . processChainEffects trace clientHandler stateVar)
        (healthcheck :<|>
         (genRandomTx :<|>
          consumeEventHistory stateVar))

data Ctx = Ctx { serverHandler :: Server.ServerHandler
               , clientHandler :: Client.ClientHandler
               , serverState   :: MVar AppState
               , mockTrace     :: Trace IO MockServerLogMsg
               }

main :: Trace IO MockServerLogMsg -> MockServerConfig -> Availability -> IO ()
main trace MockServerConfig { mscBaseUrl
                            , mscRandomTxInterval
                            , mscBlockReaper
                            , mscKeptBlocks
                            , mscSlotLength
                            , mscInitialTxWallets
                            , mscSocketPath } availability = LM.runLogEffects trace $ do

    -- make initial distribution of 1 billion Ada to all configured wallets
    let dist = Map.fromList $ zip mscInitialTxWallets (repeat (Ada.adaValueOf 1000_000_000))
    let appState = AppState
            { _chainState = initialChainState dist
            , _eventHistory = mempty
            }
    serverHandler <- liftIO $ Server.runServerNode mscSocketPath mscKeptBlocks (_chainState appState)
    serverState   <- liftIO $ newMVar appState
    handleDelayEffect $ delayThread (2 :: Second)
    clientHandler <- liftIO $ Client.runClientNode mscSocketPath (updateChainState serverState)

    let ctx = Ctx serverHandler clientHandler serverState trace

    runSlotCoordinator ctx mscSlotLength
    maybe (logInfo NoRandomTxGeneration) (runRandomTxGeneration ctx) mscRandomTxInterval
    maybe (logInfo KeepingOldBlocks) (runBlockReaper ctx) mscBlockReaper

    logInfo $ StartingMockServer $ baseUrlPort mscBaseUrl
    liftIO $ Warp.runSettings warpSettings $ app trace clientHandler serverState

        where
            warpSettings = Warp.defaultSettings & Warp.setPort (baseUrlPort mscBaseUrl) & Warp.setBeforeMainLoop (available availability)

            runRandomTxGeneration Ctx { clientHandler , serverState , mockTrace } randomTxInterval = do
                    logInfo StartingRandomTx
                    void $ liftIO $ forkIO $ transactionGenerator mockTrace randomTxInterval clientHandler serverState

            runBlockReaper Ctx { serverHandler } reaperConfig = do
                logInfo RemovingOldBlocks
                void $ liftIO $ forkIO $ blockReaper reaperConfig serverHandler

            runSlotCoordinator Ctx { serverHandler } slotLength = do
                logInfo StartingSlotCoordination
                void $ liftIO $ forkIO $ slotCoordinator slotLength serverHandler

            updateChainState :: MVar AppState -> Block -> Slot -> IO ()
            updateChainState mv block slot =
                modifyMVar_ mv $ pure .
                  over (chainState . chainNewestFirst) (block :) .
                  set  (chainState . currentSlot     ) slot

