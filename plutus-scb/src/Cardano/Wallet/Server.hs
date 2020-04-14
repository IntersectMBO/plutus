{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}

module Cardano.Wallet.Server
    ( main
    , Config(..)
    ) where

import qualified Cardano.Node.Client           as NodeClient
import           Cardano.Node.Follower         (NodeFollowerEffect)
import           Cardano.Wallet.API            (API)
import           Cardano.Wallet.Mock
import           Cardano.Wallet.Types          (Config (..))
import           Control.Concurrent.MVar       (MVar, newMVar, putMVar, takeMVar)
import qualified Control.Monad.Except          as MonadError
import           Control.Monad.Freer           (Eff, runM)
import           Control.Monad.Freer.Error     (Error, handleError, runError, throwError)
import           Control.Monad.Freer.Extra.Log (Log, runStderrLog)
import           Control.Monad.Freer.Reader    (Reader, runReader)
import           Control.Monad.Freer.State     (State, runState)
import           Control.Monad.IO.Class        (MonadIO, liftIO)
import qualified Data.ByteString.Lazy.Char8    as Char8
import           Data.Proxy                    (Proxy (Proxy))
import           Network.HTTP.Client           (defaultManagerSettings, newManager)
import           Network.Wai.Handler.Warp      (run)
import           Plutus.SCB.Arbitrary          ()
import           Servant                       ((:<|>) ((:<|>)), Application, Handler (Handler), ServerError (..),
                                                err400, hoistServer, serve)
import           Servant.Client                (BaseUrl (baseUrlPort), ClientEnv, ClientError, mkClientEnv)
import           Servant.Extra                 (capture)

type AppEffects m = '[NodeFollowerEffect, State MockWalletState, Log, Reader ClientEnv, Error ClientError, Error ServerError, m]

runAppEffects ::
    ( MonadIO m
    )
    => ClientEnv
    -> MockWalletState
    -> Eff (AppEffects m) a
    -> m (Either ServerError (a, MockWalletState))
runAppEffects clientEnv mockWalletState action =
    runM
            $ runError
            $ flip handleError (\e -> throwError $ err400 { errBody = Char8.pack (show e) })
            $ runReader clientEnv
            $ runStderrLog
            $ runState mockWalletState
            $ NodeClient.handleNodeFollowerClient clientEnv action

------------------------------------------------------------
-- | Run all handlers, affecting a single, global 'MVar State'.
--
-- Note this code is pretty simplistic, as it makes every handler
-- block on access to a single, global 'MVar'.  We could do something
-- smarter, but I don't think it matters as this is only a mock.
asHandler ::
    ClientEnv
    -> MVar MockWalletState
    -> Eff (AppEffects IO) a
    -> Handler a
asHandler nodeClientEnv mVarState action =
    Handler $ do
        oldState <- liftIO $ takeMVar mVarState
        result <- liftIO $ runAppEffects nodeClientEnv oldState action
        case result of
            Left err -> do
                liftIO $ putMVar mVarState oldState
                MonadError.throwError $ err400 { errBody = Char8.pack (show err) }
            Right (result_, newState) -> do
                liftIO $ putMVar mVarState newState
                pure result_

app :: ClientEnv -> MVar MockWalletState -> Application
app nodeClientEnv mVarState =
    serve (Proxy @API) $
    hoistServer (Proxy @API) (asHandler nodeClientEnv mVarState) $
    wallets :<|> getOwnPubKey :<|> getWatchedAddresses :<|> startWatching :<|>
    capture (selectCoin :<|> allocateAddress) :<|> valueAt

main :: (MonadIO m) => Config -> BaseUrl -> m ()
main Config {baseUrl} nodeBaseUrl = do
    let port = baseUrlPort baseUrl
    nodeClientEnv <-
        liftIO $ do
            nodeManager <- newManager defaultManagerSettings
            pure $ mkClientEnv nodeManager nodeBaseUrl
    (_, populatedState) <- either (error . show) pure =<< runAppEffects nodeClientEnv initialState syncState
    mVarState <- liftIO $ newMVar populatedState
    liftIO $ run port $ app nodeClientEnv mVarState
