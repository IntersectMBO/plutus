{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

module Cardano.Wallet.MultiUserServer
    ( main
    , Config(..)
    ) where

import           Cardano.BM.Data.Trace           (Trace)
import qualified Cardano.ChainIndex.Client       as ChainIndexClient
import qualified Cardano.Node.Client             as NodeClient
import           Cardano.Wallet.API              (API)
import           Cardano.Wallet.Mock
import           Cardano.Wallet.Types            (ChainIndexUrl, Config (..), NodeUrl, WalletMsg (..), Wallets)
import           Control.Concurrent.Availability (Availability, available)
import           Control.Concurrent.MVar         (MVar, newMVar, putMVar, takeMVar)
import           Control.Monad                   ((>=>))
import qualified Control.Monad.Except            as MonadError
import           Control.Monad.Freer
import           Control.Monad.Freer.Error       (Error, handleError, runError, throwError)
import           Control.Monad.Freer.Extra.Log   (LogMsg, logInfo, runStderrLog)
import           Control.Monad.Freer.Extras      (raiseEnd)
import           Control.Monad.Freer.State       (State, get, put, runState)
import           Control.Monad.IO.Class          (MonadIO, liftIO)
import qualified Data.ByteString.Lazy.Char8      as Char8
import           Data.Function                   ((&))
import qualified Data.Map.Strict                 as Map
import           Data.Proxy                      (Proxy (Proxy))
import           Data.Text                       (Text)
import           Network.HTTP.Client             (defaultManagerSettings, newManager)
import qualified Network.Wai.Handler.Warp        as Warp
import           Plutus.PAB.Arbitrary            ()
import           Servant                         (Application, Handler (Handler), NoContent (..), ServerError (..),
                                                  err400, err500, hoistServer, serve, (:<|>) ((:<|>)))
import           Servant.Client                  (BaseUrl (baseUrlPort), ClientEnv, ClientError, mkClientEnv)
import qualified Wallet.API                      as WAPI

import           Plutus.PAB.Monitoring           (runLogEffects)
import           Wallet.Effects                  (ChainIndexEffect, MultiWalletEffect (..), NodeClientEffect,
                                                  WalletEffect, multiWallet, ownOutputs, ownPubKey, startWatching,
                                                  submitTxn, updatePaymentWithChange, walletSlot)
import           Wallet.Emulator.Error           (WalletAPIError)
import           Wallet.Emulator.Wallet          (WalletState, emptyWalletState)
import qualified Wallet.Emulator.Wallet          as Wallet

type AppEffects m = '[MultiWalletEffect, NodeClientEffect, ChainIndexEffect, State Wallets, LogMsg Text, Error WalletAPIError, Error ClientError, Error ServerError, m]

runAppEffects ::
    ( MonadIO m
    )
    => ClientEnv
    -> ClientEnv
    -> Wallets
    -> Eff (AppEffects m) a
    -> m (Either ServerError (a, Wallets))
runAppEffects nodeClientEnv chainIndexEnv wallets action =
    runM
            $ runError
            $ flip handleError (\e -> throwError $ err500 { errBody = Char8.pack (show e) })
            $ flip handleError (throwError . fromWalletAPIError)
            $ runStderrLog
            $ runState wallets
            $ ChainIndexClient.handleChainIndexClient chainIndexEnv
            $ NodeClient.handleNodeClientClient nodeClientEnv
            $ handleMutliWallet action


handleMutliWallet :: forall effs. ( Member NodeClientEffect effs
    , Member ChainIndexEffect effs
    , Member (State Wallets) effs
    , Member (Error WAPI.WalletAPIError) effs
    ) => Eff (MultiWalletEffect ': effs) ~> Eff effs
handleMutliWallet = do
    interpret $ \(MultiWallet wid action) -> do
        wallets <- get @Wallets

        case Map.lookup wid wallets of
            Just (ws, privKey) -> do
                (s, ws') <- (runState ws $ (action
                    & raiseEnd @(State WalletState ': effs)
                    & Wallet.handleWallet))
                put $ Map.insert wid (ws', privKey) wallets
                return s
            Nothing -> undefined

------------------------------------------------------------
-- | Run all handlers, affecting a single, global 'MVar WalletState'.
--
-- Note this code is pretty simplistic, as it makes every handler
-- block on access to a single, global 'MVar'.  We could do something
-- smarter, but I don't think it matters as this is only a mock.

asHandler ::
    ClientEnv
    -> ClientEnv
    -> MVar Wallets
    -> Eff (AppEffects IO) a
    -> Handler a
asHandler nodeClientEnv chainIndexEnv mVarState action =
    Handler $ do
        oldState <- liftIO $ takeMVar mVarState
        result <- liftIO $ runAppEffects nodeClientEnv chainIndexEnv oldState action
        case result of
            Left err -> do
                liftIO $ putMVar mVarState oldState
                MonadError.throwError $ err400 { errBody = Char8.pack (show err) }
            Right (result_, newState) -> do
                liftIO $ putMVar mVarState newState
                pure result_

app :: ClientEnv -> ClientEnv -> MVar Wallets -> Application
app nodeClientEnv chainIndexEnv mVarState =
    serve (Proxy @API) $
    hoistServer (Proxy @API) (asHandler nodeClientEnv chainIndexEnv mVarState) $
    (\w tx -> multiWallet w (submitTxn tx) >>= const (pure NoContent)) :<|> (\w -> multiWallet w ownPubKey) :<|> (\w -> multiWallet w . (uncurry updatePaymentWithChange)) :<|>
        (\w -> multiWallet w walletSlot) :<|> (\w -> multiWallet w ownOutputs)

main :: Trace IO WalletMsg -> Config -> NodeUrl -> ChainIndexUrl -> Availability -> IO ()
main trace Config {..} nodeBaseUrl chainIndexBaseUrl availability = runLogEffects trace $ do
    nodeClientEnv <- buildEnv nodeBaseUrl defaultManagerSettings
    chainIndexEnv <- buildEnv chainIndexBaseUrl defaultManagerSettings
    mVarState <- liftIO $ newMVar state
    -- runClient chainIndexEnv
    logInfo $ StartingWallet servicePort
    liftIO $ Warp.runSettings warpSettings $ app nodeClientEnv chainIndexEnv mVarState
    where
        servicePort = baseUrlPort baseUrl
        state = mempty
        -- state = emptyWalletState wallet
        warpSettings = Warp.defaultSettings & Warp.setPort servicePort & Warp.setBeforeMainLoop (available availability)

        buildEnv url settings = liftIO
            $ newManager settings >>= \mgr -> pure $ mkClientEnv mgr url

        {- `runClient env = liftIO
             $ runM
             $ flip handleError (error . show @ClientError)
             $ ChainIndexClient.handleChainIndexClient env
             $ startWatching (Wallet.ownAddress state)` -}
