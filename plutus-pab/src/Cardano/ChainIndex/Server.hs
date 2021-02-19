{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}
module Cardano.ChainIndex.Server(
    -- $chainIndex
    main
    , ChainIndexConfig(..)
    , ChainIndexServerMsg
    , syncState
    ) where

import           Cardano.BM.Data.Trace            (Trace)
import           Cardano.Node.Types               (FollowerID, NodeFollowerEffect, getBlocks, getSlot, newFollower)
import           Control.Concurrent               (forkIO, threadDelay)
import           Control.Concurrent.MVar          (MVar, newMVar, putMVar, takeMVar)
import           Control.Monad                    (forever, unless, void)
import           Control.Monad.Freer              hiding (run)
import           Control.Monad.Freer.Extras.Log
import           Control.Monad.Freer.Extras.State (assign, use)
import           Control.Monad.Freer.State
import qualified Control.Monad.Freer.State        as Eff
import           Control.Monad.IO.Class           (MonadIO (..))
import           Data.Foldable                    (fold, traverse_)
import           Data.Function                    ((&))
import           Data.Proxy                       (Proxy (Proxy))
import           Data.Time.Units                  (Second, toMicroseconds)
import           Ledger.Blockchain                (Block)
import           Network.HTTP.Client              (defaultManagerSettings, newManager)
import qualified Network.Wai.Handler.Warp         as Warp
import           Servant                          (Application, NoContent (NoContent), hoistServer, serve,
                                                   (:<|>) ((:<|>)))
import           Servant.Client                   (BaseUrl (baseUrlPort), ClientEnv, mkClientEnv, runClientM)

import           Cardano.ChainIndex.API
import           Cardano.ChainIndex.Types
import qualified Cardano.Node.Client              as NodeClient
import           Control.Concurrent.Availability  (Availability, available)
import           Ledger.Address                   (Address)
import           Ledger.AddressMap                (AddressMap)
import           Plutus.PAB.Monitoring            (convertLog, handleLogMsgTrace, runLogEffects)
import           Wallet.Effects                   (ChainIndexEffect)
import qualified Wallet.Effects                   as WalletEffects
import           Wallet.Emulator.ChainIndex       (ChainIndexControlEffect, ChainIndexEvent, ChainIndexState)
import qualified Wallet.Emulator.ChainIndex       as ChainIndex
import           Wallet.Emulator.NodeClient       (ChainClientNotification (BlockValidated, SlotChanged))

-- $chainIndex
-- The PAB chain index that keeps track of transaction data (UTXO set enriched
-- with datums)

type ChainIndexTrace = Trace IO ChainIndexServerMsg

app :: ChainIndexTrace -> MVar AppState -> Application
app trace stateVar =
    serve (Proxy @API) $
    hoistServer
        (Proxy @API)
        (liftIO . processIndexEffects trace stateVar)
        (healthcheck :<|> startWatching :<|> watchedAddresses :<|> confirmedBlocks :<|> WalletEffects.transactionConfirmed :<|> WalletEffects.nextTx)

main :: ChainIndexTrace -> ChainIndexConfig -> BaseUrl -> Availability -> IO ()
main trace ChainIndexConfig{ciBaseUrl} nodeBaseUrl availability = runLogEffects trace $ do
    nodeClientEnv <- liftIO getNode
    mVarState <- liftIO $ newMVar initialAppState

    logInfo StartingNodeClientThread
    void $ liftIO $ forkIO $ runLogEffects trace $ updateThread trace 10 mVarState nodeClientEnv

    logInfo $ StartingChainIndex servicePort
    liftIO $ Warp.runSettings warpSettings $ app trace mVarState
        where
            isAvailable = available availability
            servicePort = baseUrlPort ciBaseUrl
            warpSettings = Warp.defaultSettings & Warp.setPort servicePort & Warp.setBeforeMainLoop isAvailable
            getNode = newManager defaultManagerSettings >>= \manager -> pure $ mkClientEnv manager nodeBaseUrl


healthcheck :: Monad m => m NoContent
healthcheck = pure NoContent

startWatching :: (Member ChainIndexEffect effs) => Address -> Eff effs NoContent
startWatching addr = WalletEffects.startWatching addr >> pure NoContent

watchedAddresses :: (Member ChainIndexEffect effs) => Eff effs AddressMap
watchedAddresses = WalletEffects.watchedAddresses

confirmedBlocks :: (Member ChainIndexEffect effs) => Eff effs [Block]
confirmedBlocks = WalletEffects.confirmedBlocks


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
        maybe (logInfo ObtainingFollowerID >> newFollower >>= \i -> assign indexFollowerID (Just i) >> return i) pure
    logDebug $ UpdatingChainIndex followerID
    newBlocks <- getBlocks followerID
    logInfo $ ReceivedBlocksTxns (length newBlocks) (length $ fold newBlocks)
    currentSlot <- SlotChanged <$> getSlot
    let notifications = BlockValidated <$> newBlocks
    traverse_ ChainIndex.chainIndexNotify (notifications ++ [currentSlot])

-- | Get the latest transactions from the node and update the index accordingly
updateThread ::
    forall effs.
    ( LastMember IO effs
    , Member (LogMsg ChainIndexServerMsg) effs
    )
    => ChainIndexTrace
    -> Second
    -- ^ Interval between two queries for new blocks
    -> MVar AppState
    -- ^ State of the chain index
    -> ClientEnv
    -- ^ Servant client for the node API
    -> Eff effs ()
updateThread trace updateInterval mv nodeClientEnv = do
    logInfo ObtainingFollowerID
    followerID <-
        liftIO $
        runClientM NodeClient.newFollower nodeClientEnv >>=
        either (error . show) pure
    logInfo $ ObtainedFollowerID followerID
    forever $ do
        watching <- processIndexEffects trace mv WalletEffects.watchedAddresses
        unless (watching == mempty) (fetchNewBlocks trace followerID nodeClientEnv mv)
        liftIO $ threadDelay $ fromIntegral $ toMicroseconds updateInterval

fetchNewBlocks ::
    forall effs.
    ( LastMember IO effs
    , Member (LogMsg ChainIndexServerMsg) effs
    )
    => ChainIndexTrace
    -> FollowerID
    -> ClientEnv
    -> MVar AppState
    -> Eff effs ()
fetchNewBlocks trace followerID nodeClientEnv mv = do
    logInfo AskingNodeForNewBlocks
    newBlocks <-
        liftIO $
        runClientM (NodeClient.getBlocks followerID) nodeClientEnv >>=
        either (error . show) pure
    logInfo (ReceivedBlocksTxns (length newBlocks) (length $ fold newBlocks))
    logInfo AskingNodeForCurrentSlot
    curentSlot <-
        liftIO $
        runClientM NodeClient.getCurrentSlot nodeClientEnv >>=
        either (error . show) pure
    let notifications = BlockValidated <$> newBlocks
    traverse_
        (processIndexEffects trace mv . ChainIndex.chainIndexNotify)
        (notifications ++ [SlotChanged curentSlot])

type ChainIndexEffects m
     = '[ ChainIndexControlEffect
        , ChainIndexEffect
        , State ChainIndexState
        , LogMsg ChainIndexEvent
        , m
        ]

processIndexEffects ::
    MonadIO m
    => ChainIndexTrace
    -> MVar AppState
    -> Eff (ChainIndexEffects IO) a
    -> m a
processIndexEffects trace stateVar eff = do
    AppState {_indexState, _indexEvents, _indexFollowerID} <- liftIO $ takeMVar stateVar
    (result, newState) <- liftIO
        $ ChainIndex.handleChainIndexControl eff
        & ChainIndex.handleChainIndex
        & Eff.runState _indexState
        & handleLogMsgTrace (toChainIndexServerMsg trace)
        & runM
    liftIO $ putMVar stateVar AppState{_indexState=newState, _indexEvents=_indexEvents, _indexFollowerID=_indexFollowerID  }
    pure result
        where
            toChainIndexServerMsg :: Trace m ChainIndexServerMsg -> Trace m ChainIndexEvent
            toChainIndexServerMsg = convertLog ChainEvent
