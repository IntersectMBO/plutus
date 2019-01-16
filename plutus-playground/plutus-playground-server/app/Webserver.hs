{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
{-# OPTIONS_GHC   -Wno-orphans #-}

module Webserver
  ( run
  ) where

import qualified Auth
import           Control.Monad.Except                 (ExceptT)
import           Control.Monad.IO.Class               (MonadIO, liftIO)
import           Control.Monad.Logger                 (LoggingT, MonadLogger, logInfoN, runStderrLoggingT)
import           Data.Default.Class                   (def)
import           Data.Proxy                           (Proxy (Proxy))
import           Data.Text                            (Text)
import           Development.GitRev                   (gitHash)
import           Network.HTTP.Types                   (Method)
import           Network.Wai                          (Application)
import           Network.Wai.Handler.Warp             (Settings, runSettings)
import           Network.Wai.Middleware.Cors          (cors, corsRequestHeaders, simpleCorsResourcePolicy)
import           Network.Wai.Middleware.Gzip          (gzip)
import           Network.Wai.Middleware.RequestLogger (logStdout)
import qualified Playground.API                       as PA
import qualified Playground.Server                    as PS
import           Servant                              ((:<|>) ((:<|>)), (:>), Get, Handler (Handler), JSON, PlainText,
                                                       Raw, ServantErr, hoistServer, serve, serveDirectoryFileServer)
import           Servant.Client                       (parseBaseUrl)
import           Servant.Foreign                      (GenerateList, NoContent, Req, generateList)
import           Servant.Server                       (Server)
import qualified Web.JWT                              as JWT

instance GenerateList NoContent (Method -> Req NoContent) where
  generateList _ = []

type Web
   = "version" :> Get '[ PlainText, JSON] Text
     :<|> "api" :> (PA.API
                    :<|> Auth.API)
     :<|> Raw

liftedAuthServer :: Auth.Config -> Server Auth.API
liftedAuthServer config =
  hoistServer (Proxy @Auth.API) liftAuthToHandler $ Auth.server config
  where
    liftAuthToHandler :: LoggingT (ExceptT ServantErr IO) a -> Handler a
    liftAuthToHandler = Handler . runStderrLoggingT

server :: Server PA.API -> FilePath -> Auth.Config -> Server Web
server handlers staticDir config =
  version :<|> (handlers :<|> liftedAuthServer config) :<|>
  serveDirectoryFileServer staticDir

version :: Applicative m => m Text
version = pure $(gitHash)

app :: Server PA.API -> Auth.Config -> FilePath -> Application
app handlers config staticDir =
  gzip def . logStdout . cors (const $ Just policy) . serve (Proxy @Web) $
  server handlers staticDir config
  where
    policy =
      simpleCorsResourcePolicy
        {corsRequestHeaders = ["content-type", "set-cookie"]}

run :: (MonadLogger m, MonadIO m) => Settings -> FilePath -> m ()
run settings staticDir = do
  config <- liftIO mkTempConfig
  handlers <- PS.mkHandlers
  logInfoN "Starting webserver."
  liftIO . runSettings settings $ app handlers config staticDir

{-# DEPRECATED
mkTempConfig "This is scaffolding."
 #-}

mkTempConfig :: IO Auth.Config
mkTempConfig = do
  let _configGithubAuthLocation =
        "https://github.com/login/oauth/authorize?redirect_uri=" <> callbackUrl <>
        "&scope=gist&client_id=869cbadc1d2dfc393466&state=" <>
        Auth.tmpStateToken
      _configSigner =
        JWT.hmacSecret
          "13e36bb4deea98975b7b0d5ac318db60185001c235e5cd945b5dc5adda5816642680c5f34483a4bb"
      _configRedirectUrl = "https://localhost:8009"
      callbackUrl = _configRedirectUrl <> "/api/oauth/github/callback"
      _configClientId = "869cbadc1d2dfc393466"
      _configClientSecret = "ac912971fb52a53a96cd110ca5f86878febfaf30"
  _configGithubApiBaseUrl <- parseBaseUrl "https://api.github.com"
  pure Auth.Config {..}
