{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE TypeApplications      #-}

module Cardano.Wallet.Server
    ( main
    , Config(..)
    ) where

import qualified Cardano.ChainIndex.Client     as ChainIndexClient
import qualified Cardano.Node.Client           as NodeClient
import           Cardano.Wallet.API            (API)
import           Cardano.Wallet.Mock
import           Cardano.Wallet.Types          (Config (..))
import           Control.Concurrent.MVar       (MVar, newMVar, putMVar, takeMVar)
import           Control.Monad                 ((>=>))
import qualified Control.Monad.Except          as MonadError
import           Control.Monad.Freer           (Eff, runM)
import           Control.Monad.Freer.Error     (Error, handleError, runError, throwError)
import           Control.Monad.Freer.Extra.Log (Log, runStderrLog)
import           Control.Monad.Freer.State     (State, runState)
import           Control.Monad.IO.Class        (MonadIO, liftIO)
import qualified Data.ByteString.Lazy.Char8    as Char8
import           Data.Proxy                    (Proxy (Proxy))
import           Network.HTTP.Client           (defaultManagerSettings, newManager)
import           Network.Wai.Handler.Warp      (run)
import           Plutus.SCB.Arbitrary          ()
import           Servant                       ((:<|>) ((:<|>)), Application, Handler (Handler), NoContent (..),
                                                ServerError (..), err400, err500, hoistServer, serve)
import           Servant.Client                (BaseUrl (baseUrlPort), ClientEnv, ClientError, mkClientEnv)

import           Wallet.Effects                (ChainIndexEffect, NodeClientEffect, WalletEffect, ownOutputs, ownPubKey,
                                                startWatching, submitTxn, updatePaymentWithChange, walletSlot)
import           Wallet.Emulator.Error         (WalletAPIError)
import           Wallet.Emulator.Wallet        (WalletState)
import qualified Wallet.Emulator.Wallet        as Wallet

type AppEffects m = '[WalletEffect, NodeClientEffect, ChainIndexEffect, State WalletState, Log, Error WalletAPIError, Error ClientError, Error ServerError, m]

runAppEffects ::
    ( MonadIO m
    )
    => ClientEnv
    -> ClientEnv
    -> WalletState
    -> Eff (AppEffects m) a
    -> m (Either ServerError (a, WalletState))
runAppEffects nodeClientEnv chainIndexEnv walletState action =
    runM
            $ runError
            $ flip handleError (\e -> throwError $ err500 { errBody = Char8.pack (show e) })
            $ flip handleError (throwError . fromWalletAPIError)
            $ runStderrLog
            $ runState walletState
            $ ChainIndexClient.handleChainIndexClient chainIndexEnv
            $ NodeClient.handleNodeClientClient nodeClientEnv
            $ Wallet.handleWallet action

------------------------------------------------------------
-- | Run all handlers, affecting a single, global 'MVar WalletState'.
--
-- Note this code is pretty simplistic, as it makes every handler
-- block on access to a single, global 'MVar'.  We could do something
-- smarter, but I don't think it matters as this is only a mock.
asHandler ::
    ClientEnv
    -> ClientEnv
    -> MVar WalletState
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

app :: ClientEnv -> ClientEnv -> MVar WalletState -> Application
app nodeClientEnv chainIndexEnv mVarState =
    serve (Proxy @API) $
    hoistServer (Proxy @API) (asHandler nodeClientEnv chainIndexEnv mVarState) $
    (submitTxn >=> const (pure NoContent)) :<|> ownPubKey :<|> uncurry updatePaymentWithChange :<|>
    walletSlot :<|> ownOutputs

main :: (MonadIO m) => Config -> BaseUrl -> BaseUrl -> m ()
main Config {baseUrl} nodeBaseUrl chainIndexBaseUrl = do
    let port = baseUrlPort baseUrl
    nodeClientEnv <-
        liftIO $ do
            nodeManager <- newManager defaultManagerSettings
            pure $ mkClientEnv nodeManager nodeBaseUrl
    chainIndexEnv <-
        liftIO $ do
            chainIndexManager <- newManager defaultManagerSettings
            pure $ mkClientEnv chainIndexManager chainIndexBaseUrl
    mVarState <- liftIO $ newMVar initialState
    _ <- liftIO
            $ runM
            $ flip handleError (error . show @ClientError)
            $ ChainIndexClient.handleChainIndexClient chainIndexEnv
            $ startWatching (Wallet.ownAddress initialState)
    liftIO $ run port $ app nodeClientEnv chainIndexEnv mVarState
