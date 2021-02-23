{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Plutus.PAB.Webserver.Server
    ( main
    ) where

import qualified Cardano.BM.Configuration.Model   as CM
import           Cardano.BM.Trace                 (Trace)
import           Control.Concurrent.Availability  (Availability, available)
import           Control.Monad.Except             (ExceptT (ExceptT))
import           Control.Monad.Freer              (Eff, interpret)
import           Control.Monad.Freer.Extras.Log   (LogMsg, logInfo, mapLog)
import           Control.Monad.IO.Class           (liftIO)
import           Data.Bifunctor                   (first)
import qualified Data.ByteString.Lazy.Char8       as LBS
import           Data.Function                    ((&))
import           Data.Proxy                       (Proxy (Proxy))
import qualified Data.Text.Encoding               as Text
import qualified Network.Wai.Handler.Warp         as Warp
import           Plutus.PAB.App                   (App, AppBackend, runApp)
import           Plutus.PAB.Arbitrary             ()
import           Plutus.PAB.Core.ContractInstance (ContractInstanceMsg)
import           Plutus.PAB.PABLogMsg             (ContractExeLogMsg (StartingPABBackendServer), PABLogMsg (..))
import           Plutus.PAB.ParseStringifiedJSON  (UnStringifyJSONLog)
import           Plutus.PAB.Types                 (Config, ContractExe, PABError (InvalidUUIDError), baseUrl,
                                                   pabWebserverConfig, staticDir)
import           Plutus.PAB.Webserver.API         (API, WSAPI)
import           Plutus.PAB.Webserver.Handler     (handler)
import           Plutus.PAB.Webserver.Types       (WebSocketLogMsg)
import           Plutus.PAB.Webserver.WebSocket   (handleWS)
import           Servant                          (Application, Handler (Handler), Raw, ServerT, err400, err500,
                                                   errBody, hoistServer, serve, serveDirectoryFileServer,
                                                   (:<|>) ((:<|>)))
import           Servant.Client                   (BaseUrl (baseUrlPort))

asHandler :: Trace IO PABLogMsg -> CM.Configuration -> Config -> Eff (LogMsg ContractExeLogMsg ': LogMsg (ContractInstanceMsg ContractExe) ': LogMsg WebSocketLogMsg ': LogMsg UnStringifyJSONLog ': AppBackend _) a -> Handler a
asHandler trace logConfig config =
    Handler . ExceptT . fmap (first decodeErr)
      . runApp trace logConfig config
      . interpret (mapLog SUnstringifyJSON)
      . interpret (mapLog SWebsocketMsg)
      . interpret (mapLog SContractInstanceMsg)
      . interpret (mapLog SContractExeLogMsg)
  where
    decodeErr (InvalidUUIDError t) =
        err400
            {errBody = "Invalid UUID: " <> LBS.fromStrict (Text.encodeUtf8 t)}
    decodeErr err = err500 {errBody = LBS.pack $ show err}

app :: Trace IO PABLogMsg -> CM.Configuration -> Config -> Application
app trace logConfig config = serve rest (apiServer :<|> fileServer)
  where
    rest = Proxy @((API ContractExe :<|> WSAPI) :<|> Raw)
    apiServer :: ServerT (API ContractExe :<|> WSAPI) Handler
    apiServer =
      hoistServer
        (Proxy @(API ContractExe :<|> WSAPI))
        (asHandler trace logConfig config)
        (handler :<|> handleWS trace logConfig)
    fileServer :: ServerT Raw Handler
    fileServer = serveDirectoryFileServer (staticDir . pabWebserverConfig $ config)

main :: Trace IO PABLogMsg -> CM.Configuration -> Config -> Availability -> App ()
main trace logConfig config availability = interpret (mapLog SContractExeLogMsg) $ do
    let port = baseUrlPort $ baseUrl $ pabWebserverConfig config
    let warpSettings :: Warp.Settings
        warpSettings = Warp.defaultSettings & Warp.setPort port & Warp.setBeforeMainLoop (available availability)
    logInfo $ StartingPABBackendServer port
    liftIO $ Warp.runSettings warpSettings $ app trace logConfig config
