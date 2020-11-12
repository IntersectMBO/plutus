{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

module Plutus.SCB.Webserver.Server
    ( main
    ) where

import qualified Cardano.BM.Configuration.Model  as CM
import           Cardano.BM.Trace                (Trace)
import           Control.Concurrent.Availability (Availability, available)
import           Control.Monad.Except            (ExceptT (ExceptT))
import           Control.Monad.Freer.Extra.Log   (logInfo)
import           Control.Monad.IO.Class          (liftIO)
import           Data.Bifunctor                  (first)
import qualified Data.ByteString.Lazy.Char8      as LBS
import           Data.Function                   ((&))
import           Data.Proxy                      (Proxy (Proxy))
import qualified Data.Text.Encoding              as Text
import qualified Network.Wai.Handler.Warp        as Warp
import           Plutus.SCB.App                  (App, runApp)
import           Plutus.SCB.Arbitrary            ()
import           Plutus.SCB.SCBLogMsg            (ContractExeLogMsg (StartingSCBBackendServer), SCBLogMsg)
import           Plutus.SCB.Swagger              (Swagger, SwaggerAPI)
import qualified Plutus.SCB.Swagger              as Swagger
import           Plutus.SCB.Types                (Config, ContractExe, SCBError (InvalidUUIDError), baseUrl,
                                                  scbWebserverConfig, staticDir)
import           Plutus.SCB.Webserver.API        (API, DocumentationAPI, WSAPI)
import           Plutus.SCB.Webserver.Handler    (handler)
import           Plutus.SCB.Webserver.WebSocket  (handleWS)
import           Servant                         (Application, Handler (Handler), Raw, ServerT, err400, err500, errBody,
                                                  hoistServer, serve, serveDirectoryFileServer, (:<|>) ((:<|>)))
import           Servant.Client                  (BaseUrl (baseUrlPort))

asHandler :: Trace IO SCBLogMsg -> CM.Configuration -> Config -> App a -> Handler a
asHandler trace logConfig config =
    Handler . ExceptT . fmap (first decodeErr) . runApp trace logConfig config
  where
    decodeErr (InvalidUUIDError t) =
        err400
            {errBody = "Invalid UUID: " <> LBS.fromStrict (Text.encodeUtf8 t)}
    decodeErr err = err500 {errBody = LBS.pack $ show err}

app :: Trace IO SCBLogMsg -> CM.Configuration -> Config -> Application
app trace logConfig config = serve rest (apiServer :<|> swaggerServer :<|> fileServer)
  where
    rest = Proxy @((API ContractExe :<|> WSAPI) :<|> SwaggerAPI :<|> Raw)
    apiServer :: ServerT (API ContractExe :<|> WSAPI) Handler
    apiServer =
      hoistServer
        (Proxy @(API ContractExe :<|> WSAPI))
        (asHandler trace logConfig config)
        (handler :<|> handleWS trace logConfig)
    fileServer :: ServerT Raw Handler
    fileServer = serveDirectoryFileServer (staticDir . scbWebserverConfig $ config)
    swaggerServer :: Handler Swagger
    swaggerServer = Swagger.handler (Proxy @(DocumentationAPI ContractExe))

main :: Trace IO SCBLogMsg -> CM.Configuration -> Config -> Availability -> App ()
main trace logConfig config availability = do
    let port = baseUrlPort $ baseUrl $ scbWebserverConfig config
    let warpSettings :: Warp.Settings
        warpSettings = Warp.defaultSettings & Warp.setPort port & Warp.setBeforeMainLoop (available availability)
    logInfo $ StartingSCBBackendServer port
    liftIO $ Warp.runSettings warpSettings $ app trace logConfig config
