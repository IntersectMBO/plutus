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

import qualified API                                            as MA
import qualified Auth
import           Control.Concurrent                             (forkIO)
import           Control.Monad                                  (void)
import           Control.Monad.Except                           (ExceptT)
import           Control.Monad.IO.Class                         (MonadIO, liftIO)
import           Control.Monad.Logger                           (LoggingT, MonadLogger, logInfoN, runStderrLoggingT)
import           Control.Monad.Reader                           (ReaderT, runReaderT)
import           Data.Default.Class                             (def)
import           Data.Proxy                                     (Proxy (Proxy))
import           Data.Text                                      (Text)
import           Development.GitRev                             (gitHash)
import           Network.HTTP.Types                             (Method)
import           Network.Wai                                    (Application)
import           Network.Wai.Handler.Warp                       (Settings, runSettings)
import           Network.Wai.Middleware.Cors                    (cors, corsRequestHeaders, simpleCorsResourcePolicy)
import           Network.Wai.Middleware.Gzip                    (gzip)
import           Network.Wai.Middleware.RequestLogger           (logStdout)
import           Servant                                        ((:<|>) ((:<|>)), (:>), Get, Handler (Handler), JSON,
                                                                 PlainText, Raw, ServantErr, hoistServer, serve,
                                                                 serveDirectoryFileServer)
import           Servant.Foreign                                (GenerateList, NoContent, Req, generateList)
import           Servant.Prometheus                             (monitorEndpoints)
import           Servant.Server                                 (Server)
import           Server                                         (mkHandlers)
import           System.Metrics.Prometheus.Concurrent.RegistryT (runRegistryT)
import           System.Metrics.Prometheus.Http.Scrape          (serveHttpTextMetricsT)
import           Types                                          (Config (Config, _authConfig))

instance GenerateList NoContent (Method -> Req NoContent) where
  generateList _ = []

type Web
   = "version" :> Get '[ PlainText, JSON] Text
     :<|> "api" :> (MA.API
                    :<|> Auth.API)
     :<|> Raw

liftedAuthServer :: Auth.GithubEndpoints -> Auth.Config -> Server Auth.API
liftedAuthServer githubEndpoints config =
  hoistServer (Proxy @Auth.API) liftAuthToHandler Auth.server
  where
    liftAuthToHandler ::
         ReaderT (Auth.GithubEndpoints, Auth.Config) (LoggingT (ExceptT ServantErr IO)) a
      -> Handler a
    liftAuthToHandler =
      Handler . runStderrLoggingT . flip runReaderT (githubEndpoints, config)

server ::
     Server MA.API -> FilePath -> Auth.GithubEndpoints -> Config -> Server Web
server handlers _staticDir githubEndpoints Config {..} =
  version :<|> (handlers :<|> liftedAuthServer githubEndpoints _authConfig) :<|>
  serveDirectoryFileServer _staticDir

version :: Applicative m => m Text
version = pure $(gitHash)

app ::
     Server MA.API -> FilePath -> Auth.GithubEndpoints -> Config -> Application
app handlers _staticDir githubEndpoints config =
  gzip def . logStdout . cors (const $ Just policy) . serve (Proxy @Web) $
  server handlers _staticDir githubEndpoints config
  where
    policy =
      simpleCorsResourcePolicy
        {corsRequestHeaders = ["content-type", "set-cookie"]}

run :: (MonadLogger m, MonadIO m) => Settings -> FilePath -> Config -> m ()
run settings _staticDir config = runRegistryT $ do
  githubEndpoints <- liftIO Auth.mkGithubEndpoints
  handlers <- mkHandlers
  appMonitor <- monitorEndpoints (Proxy @Web)
  logInfoN "Starting webserver."
  void . liftIO . forkIO . runSettings settings . appMonitor $ app handlers _staticDir githubEndpoints config
  serveHttpTextMetricsT 9091 ["metrics"]
