{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
module Cardano.ChainIndex.Server(
    -- $chainIndex
    main
    , ChainIndexConfig(..)
    , ChainIndexServerMsg(..)
    , syncState
    ) where

import           Cardano.Node.Types              (FollowerID)
import           Control.Concurrent              (forkIO, threadDelay)
import           Control.Concurrent.MVar         (MVar, newMVar, putMVar, takeMVar)
import           Control.Monad                   (forever, unless, void)
import           Control.Monad.Freer             hiding (run)
import           Control.Monad.Freer.Extra.Log
import           Control.Monad.Freer.Extra.State (assign, use)
import           Control.Monad.Freer.Log         (renderLogMessages)
import           Control.Monad.Freer.State
import qualified Control.Monad.Freer.State       as Eff
import           Control.Monad.IO.Class          (MonadIO (..))
import           Control.Monad.Logger            (MonadLogger, logDebugN, logInfoN, runStdoutLoggingT)
import           Data.Foldable                   (fold, traverse_)
import           Data.Function                   ((&))
import           Data.Proxy                      (Proxy (Proxy))
import           Data.Text                       (Text)
import           Data.Text.Prettyprint.Doc       (Pretty (..), parens, (<+>))
import           Data.Time.Units                 (Second, toMicroseconds)
import           Ledger.Blockchain               (Block)
import           Network.HTTP.Client             (defaultManagerSettings, newManager)
import qualified Network.Wai.Handler.Warp        as Warp
import           Servant                         (Application, NoContent (NoContent), hoistServer, serve,
                                                  (:<|>) ((:<|>)))
import           Servant.Client                  (BaseUrl (baseUrlPort), ClientEnv, mkClientEnv, runClientM)

import           Ledger.Address                  (Address)
import           Ledger.AddressMap               (AddressMap)
import           Plutus.PAB.Utils                (tshow)

import           Cardano.ChainIndex.API
import           Cardano.ChainIndex.Types
import qualified Cardano.Node.Client             as NodeClient
import           Cardano.Node.Follower           (NodeFollowerEffect, getSlot)
import qualified Cardano.Node.Follower           as NodeFollower
import           Control.Concurrent.Availability (Availability, available)
import           Wallet.Effects                  (ChainIndexEffect)
import qualified Wallet.Effects                  as WalletEffects
import           Wallet.Emulator.ChainIndex      (ChainIndexControlEffect, ChainIndexEvent, ChainIndexState)
import qualified Wallet.Emulator.ChainIndex      as ChainIndex
import           Wallet.Emulator.NodeClient      (ChainClientNotification (BlockValidated, SlotChanged))

-- $chainIndex
-- The PAB chain index that keeps track of transaction data (UTXO set enriched
-- with datums)

app :: MVar AppState -> Application
app stateVar =
    serve (Proxy @API) $
    hoistServer
        (Proxy @API)
        (processIndexEffects stateVar)
        (healthcheck :<|> startWatching :<|> watchedAddresses :<|> confirmedBlocks :<|> WalletEffects.transactionConfirmed :<|> WalletEffects.nextTx)

main :: MonadIO m => ChainIndexConfig -> BaseUrl -> Availability -> m ()
main ChainIndexConfig{ciBaseUrl} nodeBaseUrl availability = runStdoutLoggingT $ do
    let port = baseUrlPort ciBaseUrl
    nodeClientEnv <-
        liftIO $ do
            nodeManager <- newManager defaultManagerSettings
            pure $ mkClientEnv nodeManager nodeBaseUrl
    mVarState <- liftIO $ newMVar initialAppState
    logInfoN "Starting node client thread"
    void $ liftIO $ forkIO $ runStdoutLoggingT $ updateThread 10 mVarState nodeClientEnv
    let warpSettings :: Warp.Settings
        warpSettings = Warp.defaultSettings & Warp.setPort port & Warp.setBeforeMainLoop (available availability)
    logInfoN $ "Starting chain index on port: " <> tshow port
    liftIO $ Warp.runSettings warpSettings $ app mVarState

healthcheck :: Monad m => m NoContent
healthcheck = pure NoContent

startWatching :: (Member ChainIndexEffect effs) => Address -> Eff effs NoContent
startWatching addr = WalletEffects.startWatching addr >> pure NoContent

watchedAddresses :: (Member ChainIndexEffect effs) => Eff effs AddressMap
watchedAddresses = WalletEffects.watchedAddresses

confirmedBlocks :: (Member ChainIndexEffect effs) => Eff effs [Block]
confirmedBlocks = WalletEffects.confirmedBlocks

data ChainIndexServerMsg =
    ObtainingFollowerID
    | ObtainedFollowerID FollowerID
    | UpdatingChainIndex FollowerID
    | ReceivedBlocksTxns Int Int
    | AskingNodeForNewBlocks
    | AskingNodeForCurrentSlot

instance Pretty ChainIndexServerMsg where
    pretty = \case
        ObtainingFollowerID -> "Obtaining follower ID"
        ObtainedFollowerID i -> "Obtained follower ID:" <+> pretty i
        UpdatingChainIndex i -> "Updating chain index with follower ID" <+> pretty i
        ReceivedBlocksTxns blocks txns -> "Received" <+> pretty blocks <+> "blocks" <+> parens (pretty txns <+> "transactions")
        AskingNodeForNewBlocks -> "Asking the node for new blocks"
        AskingNodeForCurrentSlot -> "Asking the node for the current slot"

-- | Update the chain index by asking the node for new blocks since the last
--   time.
syncState ::
    ( Member (State AppState) effs
    , Member (LogMsg ChainIndexServerMsg) effs
    , Member NodeFollowerEffect effs
    , Member ChainIndexControlEffect effs
    )
    => Eff effs ()
syncState = do
    followerID <- use indexFollowerID >>=
        maybe (logInfo ObtainingFollowerID >> NodeFollower.newFollower >>= \i -> assign indexFollowerID (Just i) >> return i) pure
    logDebug $ UpdatingChainIndex followerID
    newBlocks <- NodeFollower.getBlocks followerID
    logInfo $ ReceivedBlocksTxns (length newBlocks) (length $ fold newBlocks)
    currentSlot <- SlotChanged <$> getSlot
    let notifications = BlockValidated <$> newBlocks
    traverse_ ChainIndex.chainIndexNotify (notifications ++ [currentSlot])

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
    logInfoN "Asking the node for the current slot"
    curentSlot <-
        liftIO $
        runClientM NodeClient.getCurrentSlot nodeClientEnv >>=
        either (error . show) pure
    let notifications = BlockValidated <$> newBlocks
    traverse_
        (processIndexEffects mv . ChainIndex.chainIndexNotify)
        (notifications ++ [SlotChanged curentSlot])

type ChainIndexEffects m
     = '[ ChainIndexControlEffect
        , ChainIndexEffect
        , State ChainIndexState
        , LogMsg ChainIndexEvent
        , LogMsg Text
        , m
        ]

processIndexEffects ::
    MonadIO m
    => MVar AppState
    -> Eff (ChainIndexEffects IO) a
    -> m a
processIndexEffects stateVar eff = do
    AppState{_indexState, _indexEvents, _indexFollowerID} <- liftIO $ takeMVar stateVar
    (result, newState) <- liftIO
                            $ runM
                            $ runStderrLog
                            $ interpret renderLogMessages
                            $ Eff.runState _indexState
                            $ ChainIndex.handleChainIndex
                            $ ChainIndex.handleChainIndexControl eff
    liftIO $ putMVar stateVar AppState{_indexState=newState, _indexEvents=_indexEvents, _indexFollowerID=_indexFollowerID  }
    pure result
