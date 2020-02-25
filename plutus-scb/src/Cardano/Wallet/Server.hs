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

import           Cardano.Node.API          (NodeFollowerAPI (..))
import qualified Cardano.Node.Client       as NodeClient
import           Cardano.Wallet.API        (API)
import           Cardano.Wallet.Mock
import           Cardano.Wallet.Types      (Config (..))
import           Control.Concurrent.MVar   (MVar, newMVar, putMVar, takeMVar)
import           Control.Monad.Except      (ExceptT)
import           Control.Monad.IO.Class    (MonadIO, liftIO)
import           Control.Monad.Logger      (LoggingT, MonadLogger, logInfoN, runStderrLoggingT)
import           Control.Monad.State       (MonadState, StateT, execStateT, runStateT, state)
import           Control.Monad.Trans.Class (MonadTrans, lift)
import           Data.Proxy                (Proxy (Proxy))
import           Network.HTTP.Client       (defaultManagerSettings, newManager)
import           Network.Wai.Handler.Warp  (run)
import           Plutus.SCB.Arbitrary      ()
import           Plutus.SCB.Utils          (tshow)
import           Servant                   ((:<|>) ((:<|>)), Application, Handler (Handler), ServantErr, hoistServer,
                                            serve)
import           Servant.Client            (BaseUrl (baseUrlPort), ClientEnv, ClientM, mkClientEnv, runClientM)
import           Servant.Extra             (capture)

------------------------------------------------------------
-- | Run all handlers, affecting a single, global 'MVar State'.
--
-- Note this code is pretty simplistic, as it makes every handler
-- block on access to a single, global 'MVar'.  We could do something
-- smarter, but I don't think it matters as this is only a mock.
asHandler ::
       MVar State
    -> LoggingT (StateT State (ExceptT ServantErr IO)) a
    -> Handler a
asHandler mVarState action =
    Handler $ do
        oldState <- liftIO $ takeMVar mVarState
        (result, newState) <- runStateT (runStderrLoggingT action) oldState
        liftIO $ putMVar mVarState newState
        pure result

app :: MVar State -> Application
app mVarState =
    serve (Proxy @API) $
    hoistServer (Proxy @API) (asHandler mVarState) $
    wallets :<|>
    (getOwnPubKey :<|> getWatchedAddresses :<|> startWatching) :<|>
    capture (selectCoin :<|> allocateAddress)

main :: (MonadIO m, MonadLogger m) => Config -> BaseUrl -> m ()
main Config {baseUrl} nodeBaseUrl = do
    let port = baseUrlPort baseUrl
    logInfoN $ "Starting mock wallet server on port: " <> tshow port
    nodeClientEnv <-
        liftIO $ do
            nodeManager <- newManager defaultManagerSettings
            pure $ mkClientEnv nodeManager nodeBaseUrl
    let nodeClient = flip runClientApp nodeClientEnv
    let clientState = initialState
    populatedState <- nodeClient $ execStateT syncState clientState
    mVarState <- liftIO $ newMVar populatedState
    liftIO $ run port $ app mVarState

newtype ClientApp m a =
    ClientApp
        { runClientApp :: ClientEnv -> m a
        }

instance Functor m => Functor (ClientApp m) where
    fmap f (ClientApp x) = ClientApp (\env -> fmap f (x env))

instance Applicative m => Applicative (ClientApp m) where
    pure x = ClientApp (\_ -> pure x)
    (ClientApp x) <*> (ClientApp y) = ClientApp (\env -> x env <*> y env)

instance Monad m => Monad (ClientApp m) where
    a >>= b =
        ClientApp $ \env -> do
            v <- runClientApp a env
            runClientApp (b v) env

instance Monad m => MonadState state (ClientApp (StateT state m)) where
    state f = ClientApp (const (state f))

instance MonadTrans ClientApp where
    lift = ClientApp . const

instance MonadLogger m => MonadLogger (ClientApp m)

instance MonadIO m => NodeFollowerAPI (ClientApp m) where
    subscribe = liftClientM NodeClient.newFollower
    blocks = liftClientM . NodeClient.getBlocks

liftClientM :: MonadIO m => ClientM a -> ClientApp m a
liftClientM action =
    ClientApp
        (\env -> do
             result <- liftIO $ runClientM action env
             case result of
                 Right value -> pure value
                 Left err    -> error $ show err)
