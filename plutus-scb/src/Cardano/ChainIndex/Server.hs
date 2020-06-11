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
    , syncState
    ) where
import           Cardano.Node.Types              (FollowerID)
import           Control.Concurrent              (forkIO, threadDelay)
import           Control.Concurrent.MVar         (MVar, newMVar, putMVar, takeMVar)
import           Control.Monad                   (forever, unless, void)
import           Control.Monad.Freer             hiding (run)
import           Control.Monad.Freer.Extra.Log
import           Control.Monad.Freer.Extra.State (assign, use)
import           Control.Monad.Freer.State
import qualified Control.Monad.Freer.State       as Eff
import           Control.Monad.Freer.Writer
import qualified Control.Monad.Freer.Writer      as Eff
import           Control.Monad.IO.Class          (MonadIO (..))
import           Control.Monad.Logger            (MonadLogger, logDebugN, logInfoN, runStdoutLoggingT)
import           Data.Foldable                   (fold, traverse_)
import           Data.Proxy                      (Proxy (Proxy))
import qualified Data.Sequence                   as Seq
import           Data.Time.Units                 (Second, toMicroseconds)
import           Network.HTTP.Client             (defaultManagerSettings, newManager)
import           Network.Wai.Handler.Warp        (run)
import           Servant                         ((:<|>) ((:<|>)), Application, NoContent (NoContent), hoistServer,
                                                  serve)
import           Servant.Client                  (BaseUrl (baseUrlPort), ClientEnv, mkClientEnv, runClientM)

import           Ledger.Address                  (Address)
import           Ledger.AddressMap               (AddressMap)
import           Plutus.SCB.Utils                (tshow)

import           Cardano.ChainIndex.API
import           Cardano.ChainIndex.Types
import qualified Cardano.Node.Client             as NodeClient
import           Cardano.Node.Follower           (NodeFollowerEffect)
import qualified Cardano.Node.Follower           as NodeFollower
import           Wallet.Effects                  (ChainIndexEffect)
import qualified Wallet.Effects                  as WalletEffects
import           Wallet.Emulator.ChainIndex      (ChainIndexControlEffect, ChainIndexEvent, ChainIndexState)
import qualified Wallet.Emulator.ChainIndex      as ChainIndex
import           Wallet.Emulator.NodeClient      (BlockValidated (..))

-- $chainIndex
-- The SCB chain index that keeps track of transaction data (UTXO set enriched
-- with datums)

app :: MVar AppState -> Application
app stateVar =
    serve (Proxy @API) $
    hoistServer
        (Proxy @API)
        (processIndexEffects stateVar)
        (healthcheck :<|> startWatching :<|> watchedAddresses :<|> confirmedBlocks :<|> WalletEffects.transactionConfirmed)

main :: (MonadIO m) => ChainIndexConfig -> BaseUrl -> m ()
main ChainIndexConfig{ciBaseUrl} nodeBaseUrl = runStdoutLoggingT $ do
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
startWatching addr = WalletEffects.startWatching addr >> pure NoContent

watchedAddresses :: (Member ChainIndexEffect effs) => Eff effs AddressMap
watchedAddresses = WalletEffects.watchedAddresses

confirmedBlocks :: (Member ChainIndexEffect effs) => Eff effs [[Tx]]
confirmedBlocks = WalletEffects.confirmedBlocks

-- | Update the chain index by asking the node for new blocks since the last
--   time.
syncState ::
    ( Member (State AppState) effs
    , Member Log effs
    , Member NodeFollowerEffect effs
    , Member ChainIndexControlEffect effs
    )
    => Eff effs ()
syncState = do
    followerID <- use indexFollowerID >>=
        maybe (logInfo "Obtaining folllower ID" >> NodeFollower.newFollower >>= \i -> assign indexFollowerID (Just i) >> return i) pure
    logDebug $ "Updating chain index with follower ID " <> tshow followerID
    newBlocks <- NodeFollower.getBlocks followerID
    logInfo $ "Received " <> tshow (length newBlocks) <> " blocks (" <> tshow (length $ fold newBlocks) <> " transactions)"
    let notifications = BlockValidated <$> newBlocks
    traverse_ ChainIndex.chainIndexNotify notifications

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
    followerID <-
        liftIO $
        runClientM NodeClient.newFollower nodeClientEnv >>=
        either (error . show) pure
    logInfoN $ "Follower ID: " <> tshow followerID
    forever $ do
        watching <- processIndexEffects mv WalletEffects.watchedAddresses
        unless (watching == mempty) (fetchNewBlocks followerID nodeClientEnv mv)
        liftIO $ threadDelay $ fromIntegral $ toMicroseconds updateInterval

fetchNewBlocks ::
       (MonadLogger m, MonadIO m)
    => FollowerID
    -> ClientEnv
    -> MVar AppState
    -> m ()
fetchNewBlocks followerID nodeClientEnv mv = do
    logInfoN "Asking the node for new blocks"
    newBlocks <-
        liftIO $
        runClientM (NodeClient.getBlocks followerID) nodeClientEnv >>=
        either (error . show) pure
    logInfoN $ "Received " <> tshow (length newBlocks) <> " blocks (" <> tshow (length $ fold newBlocks) <> " transactions)"
    logDebugN $ tshow newBlocks
    let notifications = BlockValidated <$> newBlocks
    traverse_
        (processIndexEffects mv . ChainIndex.chainIndexNotify)
        notifications

type ChainIndexEffects m
     = '[ ChainIndexControlEffect
        , ChainIndexEffect
        , State ChainIndexState
        , Writer [ChainIndexEvent]
        , Log
        , m
        ]

processIndexEffects ::
    MonadIO m
    => MVar AppState
    -> Eff (ChainIndexEffects IO) a
    -> m a
processIndexEffects stateVar eff = do
    AppState{_indexState, _indexEvents, _indexFollowerID} <- liftIO $ takeMVar stateVar
    ((result, newState), events) <- liftIO
                            $ runM
                            $ runStderrLog
                            $ Eff.runWriter
                            $ Eff.runState _indexState
                            $ ChainIndex.handleChainIndex
                            $ ChainIndex.handleChainIndexControl eff
    liftIO $ putMVar stateVar AppState{_indexState=newState, _indexEvents=_indexEvents <> Seq.fromList events, _indexFollowerID=_indexFollowerID  }
    pure result
