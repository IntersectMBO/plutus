{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TypeApplications      #-}

module Cardano.Wallet.Server
    ( main
    , Config(..)
    ) where

import           Cardano.BM.Data.Trace           (Trace)
import qualified Cardano.ChainIndex.Client       as ChainIndexClient
import qualified Cardano.Node.Client             as NodeClient
import           Cardano.Wallet.API              (API)
import           Cardano.Wallet.Mock
import           Cardano.Wallet.Types            (ChainIndexUrl, Config (..), NodeUrl, WalletMsg (..))
import           Control.Concurrent.Availability (Availability, available)
import           Control.Concurrent.MVar         (MVar, newMVar, putMVar, takeMVar)
import           Control.Monad                   ((>=>))
import qualified Control.Monad.Except            as MonadError
import           Control.Monad.Freer             (Eff, runM)
import           Control.Monad.Freer.Error       (Error, handleError, runError, throwError)
import           Control.Monad.Freer.Extras.Log  (LogMsg, logInfo)
import           Control.Monad.Freer.State       (State, runState)
import           Control.Monad.IO.Class          (MonadIO, liftIO)
import qualified Data.ByteString.Lazy.Char8      as Char8
import           Data.Function                   ((&))
import           Data.Proxy                      (Proxy (Proxy))
import           Data.Text                       (Text)
import           Network.HTTP.Client             (defaultManagerSettings, newManager)
import qualified Network.Wai.Handler.Warp        as Warp
import           Plutus.PAB.Arbitrary            ()
import           Servant                         (Application, Handler (Handler), NoContent (..), ServerError (..),
                                                  err400, err500, hoistServer, serve, (:<|>) ((:<|>)))
import           Servant.Client                  (BaseUrl (baseUrlPort), ClientEnv, ClientError, mkClientEnv)

import           Plutus.PAB.Monitoring           (convertLog, handleLogMsgTrace, runLogEffects)
import           Wallet.Effects                  (ChainIndexEffect, NodeClientEffect, WalletEffect, ownOutputs,
                                                  ownPubKey, startWatching, submitTxn, updatePaymentWithChange,
                                                  walletSlot)
import           Wallet.Emulator.Error           (WalletAPIError)
import           Wallet.Emulator.Wallet          (WalletState, emptyWalletState)
import qualified Wallet.Emulator.Wallet          as Wallet

type AppEffects m = '[WalletEffect
                     , NodeClientEffect
                     , ChainIndexEffect
                     , State WalletState
                     , LogMsg Text
                     , Error WalletAPIError
                     , Error ClientError
                     , Error ServerError
                     , m]
runAppEffects ::
     MonadIO m
    => Trace m WalletMsg
    -> ClientEnv
    -> ClientEnv
    -> WalletState
    -> Eff (AppEffects m) a
    -> m (Either ServerError (a, WalletState))
runAppEffects trace nodeClientEnv chainIndexEnv walletState action =
    Wallet.handleWallet action
    & NodeClient.handleNodeClientClient nodeClientEnv
    & ChainIndexClient.handleChainIndexClient chainIndexEnv
    & runState walletState
    & handleLogMsgTrace (toWalletMsg trace)
    & handleWalletApiErrors
    & handleClientErrors
    & runError
    & runM
        where
            handleWalletApiErrors = flip handleError (throwError . fromWalletAPIError)
            handleClientErrors = flip handleError (\e -> throwError $ err500 { errBody = Char8.pack (show e) })
            toWalletMsg = convertLog ChainClientMsg


------------------------------------------------------------
-- | Run all handlers, affecting a single, global 'MVar WalletState'.
--
-- Note this code is pretty simplistic, as it makes every handler
-- block on access to a single, global 'MVar'.  We could do something
-- smarter, but I don't think it matters as this is only a mock.
asHandler ::
    Trace IO WalletMsg
    -> ClientEnv
    -> ClientEnv
    -> MVar WalletState
    -> Eff (AppEffects IO) a
    -> Handler a
asHandler trace nodeClientEnv chainIndexEnv mVarState action =
    Handler $ do
        oldState <- liftIO $ takeMVar mVarState
        result <- liftIO $ runAppEffects trace nodeClientEnv chainIndexEnv oldState action
        case result of
            Left err -> do
                liftIO $ putMVar mVarState oldState
                MonadError.throwError $ err400 { errBody = Char8.pack (show err) }
            Right (result_, newState) -> do
                liftIO $ putMVar mVarState newState
                pure result_

app :: Trace IO WalletMsg -> ClientEnv -> ClientEnv -> MVar WalletState -> Application
app trace nodeClientEnv chainIndexEnv mVarState =
    serve (Proxy @API) $
    hoistServer (Proxy @API) (asHandler trace nodeClientEnv chainIndexEnv mVarState) $
    (submitTxn >=> const (pure NoContent)) :<|> ownPubKey :<|> uncurry updatePaymentWithChange :<|>
    walletSlot :<|> ownOutputs

main :: Trace IO WalletMsg -> Config -> NodeUrl -> ChainIndexUrl -> Availability -> IO ()
main trace Config {..} nodeBaseUrl chainIndexBaseUrl availability = runLogEffects trace $ do
    nodeClientEnv <- buildEnv nodeBaseUrl defaultManagerSettings
    chainIndexEnv <- buildEnv chainIndexBaseUrl defaultManagerSettings
    mVarState <- liftIO $ newMVar state
    runClient chainIndexEnv
    logInfo $ StartingWallet servicePort
    liftIO $ Warp.runSettings warpSettings $ app trace nodeClientEnv chainIndexEnv mVarState
    where
        servicePort = baseUrlPort baseUrl
        state = emptyWalletState wallet
        warpSettings = Warp.defaultSettings & Warp.setPort servicePort & Warp.setBeforeMainLoop (available availability)

        buildEnv url settings = liftIO
            $ newManager settings >>= \mgr -> pure $ mkClientEnv mgr url

        runClient env = liftIO
             $ runM
             $ flip handleError (error . show @ClientError)
             $ ChainIndexClient.handleChainIndexClient env
             $ startWatching (Wallet.ownAddress state)
