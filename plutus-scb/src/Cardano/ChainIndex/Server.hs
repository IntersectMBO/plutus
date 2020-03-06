{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
module Cardano.ChainIndex.Server(
    -- $chainIndex
    main
    , ChainIndexConfig(..)
    ) where
import           Control.Concurrent            (forkIO, threadDelay)
import           Control.Concurrent.MVar       (MVar, newMVar, putMVar, takeMVar)
import           Control.Monad                 (forever, void)
import           Control.Monad.Freer           hiding (run)
import           Control.Monad.Freer.Extra.Log
import           Control.Monad.Freer.State
import qualified Control.Monad.Freer.State     as Eff
import           Control.Monad.Freer.Writer
import qualified Control.Monad.Freer.Writer    as Eff
import           Control.Monad.IO.Class        (MonadIO (..))
import           Control.Monad.Logger          (MonadLogger, logDebugN, logInfoN, runStdoutLoggingT)
import           Data.Foldable                 (traverse_)
import           Data.Proxy                    (Proxy (Proxy))
import qualified Data.Sequence                 as Seq
import           Data.Time.Units               (Second, toMicroseconds)
import           Network.HTTP.Client           (defaultManagerSettings, newManager)
import           Network.Wai.Handler.Warp      (run)
import           Servant                       ((:<|>) ((:<|>)), Application, NoContent (NoContent), hoistServer, serve)
import           Servant.Client                (BaseUrl (baseUrlPort), ClientEnv, mkClientEnv, runClientM)

import           Ledger.Address                (Address)
import           Ledger.AddressMap             (AddressMap)
import           Plutus.SCB.Utils              (tshow)

import           Cardano.ChainIndex.API
import           Cardano.ChainIndex.Types
import qualified Cardano.Node.Client           as NodeClient
import           Wallet.Emulator.ChainIndex    (ChainIndexEffect, ChainIndexEvent, ChainIndexState)
import qualified Wallet.Emulator.ChainIndex    as ChainIndex
import           Wallet.Emulator.NodeClient    (Notification (..))

-- $chainIndex
-- The SCB chain index that keeps track of transaction data (UTXO set enriched
-- with data values)

app :: MVar AppState -> Application
app stateVar =
    serve (Proxy @API) $
    hoistServer
        (Proxy @API)
        (processIndexEffects stateVar)
        (healthcheck :<|> startWatching :<|> watchedAddresses)

main :: (MonadIO m, MonadLogger m) => ChainIndexConfig -> BaseUrl -> m ()
main ChainIndexConfig{ciBaseUrl} nodeBaseUrl = do
    let port = baseUrlPort ciBaseUrl
    logInfoN $ "Starting chain index on port: " <> tshow port
    nodeClientEnv <-
        liftIO $ do
            nodeManager <- newManager defaultManagerSettings
            pure $ mkClientEnv nodeManager nodeBaseUrl
    mVarState <- liftIO $ newMVar initialAppState
    logInfoN "Starting node client thread"
    void $ liftIO $ forkIO $ runStdoutLoggingT $ updateThread 10 mVarState nodeClientEnv
    liftIO $ run port $ app mVarState

healthcheck :: Monad m => m NoContent
healthcheck = pure NoContent

startWatching :: (Member ChainIndexEffect effs) => Address -> Eff effs NoContent
startWatching addr = ChainIndex.startWatching addr >> pure NoContent

watchedAddresses :: (Member ChainIndexEffect effs) => Eff effs AddressMap
watchedAddresses = ChainIndex.watchedAddresses

-- | Get the latest transactions from the node and update the index accordingly
updateThread ::
    (MonadIO m, MonadLogger m)
    => Second
    -- ^ Interval between two queries for new blocks
    -> MVar AppState
    -- ^ State of the chain index
    -> ClientEnv
    -- ^ Servant client for the node API
    -> m ()
updateThread updateInterval mv nodeClientEnv = do
    logInfoN "Obtaining follower ID"
    followerID <- liftIO $ runClientM NodeClient.newFollower nodeClientEnv >>= either (error . show) pure
    logInfoN $ "Follower ID: " <> tshow followerID
    forever $ do
        logInfoN "Asking the node for new blocks"
        newBlocks <- liftIO $ runClientM (NodeClient.getBlocks followerID) nodeClientEnv >>= either (error . show) pure
        logInfoN $ "Received " <> tshow (length newBlocks) <> " blocks"
        logDebugN $ tshow newBlocks
        let notifications = BlockValidated <$> newBlocks
        traverse_ (processIndexEffects mv . ChainIndex.chainIndexNotify) notifications
        liftIO $ threadDelay $ fromIntegral $ toMicroseconds updateInterval

type ChainIndexEffects m
     = '[ ChainIndexEffect, State ChainIndexState, Writer [ChainIndexEvent], Log, m]

processIndexEffects ::
    MonadIO m
    => MVar AppState
    -> Eff (ChainIndexEffects IO) a
    -> m a
processIndexEffects stateVar eff = do
    AppState{_indexState, _indexEvents} <- liftIO $ takeMVar stateVar
    ((result, newState), events) <- liftIO
                            $ runM
                            $ runStderrLog
                            $ Eff.runWriter
                            $ Eff.runState _indexState
                            $ ChainIndex.handleChainIndex eff
    liftIO $ putMVar stateVar AppState{_indexState=newState, _indexEvents=_indexEvents <> Seq.fromList events }
    pure result
