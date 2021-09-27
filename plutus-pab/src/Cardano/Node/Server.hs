{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TypeApplications   #-}

module Cardano.Node.Server
    ( main
    ) where

import           Cardano.BM.Data.Trace               (Trace)
import           Cardano.Node.API                    (API)
import           Cardano.Node.Mock
import           Cardano.Node.Types
import qualified Cardano.Protocol.Socket.Mock.Client as Client
import qualified Cardano.Protocol.Socket.Mock.Server as Server
import           Control.Concurrent                  (MVar, forkIO, newMVar)
import           Control.Concurrent.Availability     (Availability, available)
import           Control.Monad                       (void)
import           Control.Monad.Freer.Delay           (delayThread, handleDelayEffect)
import           Control.Monad.Freer.Extras.Log      (logInfo)
import           Control.Monad.IO.Class              (liftIO)
import           Data.Function                       ((&))
import qualified Data.Map.Strict                     as Map
import           Data.Proxy                          (Proxy (Proxy))
import           Data.Time.Clock.POSIX               (posixSecondsToUTCTime)
import           Data.Time.Units                     (Millisecond, Second)
import qualified Ledger.Ada                          as Ada
import           Ledger.TimeSlot                     (SlotConfig (SlotConfig, scSlotLength, scSlotZeroTime))
import qualified Network.Wai.Handler.Warp            as Warp
import           Plutus.PAB.Arbitrary                ()
import qualified Plutus.PAB.Monitoring.Monitoring    as LM
import           Servant                             (Application, hoistServer, serve, (:<|>) ((:<|>)))
import           Servant.Client                      (BaseUrl (baseUrlPort))
import           Wallet.Emulator.Wallet              (fromWalletNumber)

app ::
    Trace IO MockServerLogMsg
 -> SlotConfig
 -> Client.TxSendHandle
 -> MVar AppState
 -> Application
app trace slotCfg clientHandler stateVar =
    serve (Proxy @API) $
    hoistServer
        (Proxy @API)
        (liftIO . processChainEffects trace slotCfg clientHandler stateVar)
        (healthcheck :<|> consumeEventHistory stateVar)

data Ctx = Ctx { serverHandler :: Server.ServerHandler
               , txSendHandle  :: Client.TxSendHandle
               , serverState   :: MVar AppState
               , mockTrace     :: Trace IO MockServerLogMsg
               }

main :: Trace IO MockServerLogMsg -> MockServerConfig -> Availability -> IO ()
main trace MockServerConfig { mscBaseUrl
                            , mscKeptBlocks
                            , mscSlotConfig
                            , mscInitialTxWallets
                            , mscSocketPath } availability = LM.runLogEffects trace $ do

    -- make initial distribution of 1 billion Ada to all configured wallets
    let dist = Map.fromList $ zip (fromWalletNumber <$> mscInitialTxWallets) (repeat (Ada.adaValueOf 1000_000_000))
    initialState <- initialChainState dist
    let appState = AppState
            { _chainState = initialState
            , _eventHistory = mempty
            }
    serverHandler <- liftIO $ Server.runServerNode trace mscSocketPath mscKeptBlocks (_chainState appState)
    serverState   <- liftIO $ newMVar appState
    handleDelayEffect $ delayThread (2 :: Second)
    clientHandler <- liftIO $ Client.runTxSender mscSocketPath

    let ctx = Ctx { serverHandler = serverHandler
                  , txSendHandle  = clientHandler
                  , serverState   = serverState
                  , mockTrace     = trace
                  }

    runSlotCoordinator ctx

    logInfo $ StartingMockServer $ baseUrlPort mscBaseUrl
    liftIO $ Warp.runSettings warpSettings $ app trace mscSlotConfig clientHandler serverState

        where
            warpSettings = Warp.defaultSettings & Warp.setPort (baseUrlPort mscBaseUrl) & Warp.setBeforeMainLoop (available availability)

            runSlotCoordinator (Ctx serverHandler _ _ _)  = do
                let SlotConfig{scSlotZeroTime, scSlotLength} = mscSlotConfig
                logInfo $ StartingSlotCoordination (posixSecondsToUTCTime $ realToFrac scSlotZeroTime / 1000)
                                                   (fromInteger scSlotLength :: Millisecond)
                void $ liftIO $ forkIO $ slotCoordinator mscSlotConfig serverHandler
