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

import           Control.Concurrent.Availability (Availability, available)
import           Control.Monad.Except            (ExceptT (ExceptT))
import           Control.Monad.Freer.Extra.Log   (logInfo)
import           Control.Monad.IO.Class          (liftIO)
import           Control.Monad.Logger            (LogLevel (LevelDebug))
import           Data.Bifunctor                  (first)
import qualified Data.ByteString.Lazy.Char8      as LBS
import           Data.Function                   ((&))
import           Data.Proxy                      (Proxy (Proxy))
import qualified Data.Text.Encoding              as Text
import qualified Network.Wai.Handler.Warp        as Warp
import           Plutus.SCB.App                  (App, runApp)
import           Plutus.SCB.Arbitrary            ()
import           Plutus.SCB.Types                (Config, ContractExe, SCBError (InvalidUUIDError), baseUrl,
                                                  scbWebserverConfig, staticDir)
import           Plutus.SCB.Utils                (tshow)
import           Plutus.SCB.Webserver.API        (API, WSAPI)
import           Plutus.SCB.Webserver.Handler    (handler)
import           Plutus.SCB.Webserver.WebSocket  (handleWS)
import           Servant                         ((:<|>) ((:<|>)), Application, Handler (Handler), Raw, err400, err500,
                                                  errBody, hoistServer, serve, serveDirectoryFileServer)
import           Servant.Client                  (BaseUrl (baseUrlPort))

asHandler :: Config -> App a -> Handler a
asHandler config =
    Handler . ExceptT . fmap (first decodeErr) . runApp LevelDebug config
  where
    decodeErr (InvalidUUIDError t) =
        err400
            {errBody = "Invalid UUID: " <> LBS.fromStrict (Text.encodeUtf8 t)}
    decodeErr err = err500 {errBody = LBS.pack $ show err}

app :: Config -> Application
app config = serve rest (apiServer :<|> fileServer)
  where
    rest = Proxy @((API ContractExe :<|> WSAPI) :<|> Raw)
    apiServer =
      hoistServer
        (Proxy @(API ContractExe :<|> WSAPI))
        (asHandler config)
        (handler :<|> handleWS)
    fileServer = serveDirectoryFileServer (staticDir . scbWebserverConfig $ config)

main :: Config -> Availability -> App ()
main config availability = do
    let port = baseUrlPort $ baseUrl $ scbWebserverConfig config
    let warpSettings :: Warp.Settings
        warpSettings = Warp.defaultSettings & Warp.setPort port & Warp.setBeforeMainLoop (available availability)
    logInfo $ "Starting SCB backend server on port: " <> tshow port
    liftIO $ Warp.runSettings warpSettings $ app config
