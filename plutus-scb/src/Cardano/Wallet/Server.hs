{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TypeApplications   #-}

module Cardano.Wallet.Server
    ( main
    , Config(..)
    ) where

import qualified Cardano.Node.Client      as NodeClient
import           Cardano.Wallet.API       (API)
import           Cardano.Wallet.Mock
import           Cardano.Wallet.Types     (Config (..))
import           Control.Concurrent.MVar  (MVar, newMVar, putMVar, takeMVar)
import           Control.Monad.Except     (ExceptT)
import           Control.Monad.IO.Class   (MonadIO, liftIO)
import           Control.Monad.Logger     (LoggingT, MonadLogger, logInfoN, runStderrLoggingT)
import           Control.Monad.State      (StateT, execStateT, runStateT)
import           Data.Proxy               (Proxy (Proxy))
import           Network.HTTP.Client      (defaultManagerSettings, newManager)
import           Network.Wai.Handler.Warp (run)
import           Plutus.SCB.Arbitrary     ()
import           Plutus.SCB.Utils         (tshow)
import           Servant                  ((:<|>) ((:<|>)), Application, Handler (Handler), ServantErr, hoistServer,
                                           serve)
import           Servant.Client           (BaseUrl (baseUrlPort), mkClientEnv, runClientM)
import           Servant.Extra            (capture)

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
    Handler
        (do oldState <- liftIO $ takeMVar mVarState
            (result, newState) <- runStateT (runStderrLoggingT action) oldState
            liftIO $ putMVar mVarState newState
            pure result)

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
    let getBlockchain = liftIO $ runClientM NodeClient.blockchain nodeClientEnv
    populatedState <- execStateT (syncState getBlockchain) initialState
    mVarState <- liftIO $ newMVar populatedState
    liftIO $ run port $ app mVarState
