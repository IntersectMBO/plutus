{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC   -Wno-orphans #-}

module Webserver
    ( run
    ) where

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
import           Git                                            (gitRev)
import           Network.HTTP.Types                             (Method)
import           Network.Wai                                    (Application)
import           Network.Wai.Handler.Warp                       (Settings, runSettings)
import           Network.Wai.Middleware.Cors                    (cors, corsRequestHeaders, simpleCorsResourcePolicy)
import           Network.Wai.Middleware.Gzip                    (gzip)
import           Network.Wai.Middleware.RequestLogger           (logStdout)
import qualified Playground.API                                 as PA
import qualified Playground.Server                              as PS
import           Servant                                        ((:<|>) ((:<|>)), (:>), Get, Handler (Handler), JSON,
                                                                 PlainText, Raw, ServerError, hoistServer, serve,
                                                                 serveDirectoryFileServer)
import           Servant.Foreign                                (GenerateList, NoContent, Req, generateList)
import           Servant.Prometheus                             (monitorEndpoints)
import           Servant.Server                                 (Server)
import           System.Metrics.Prometheus.Concurrent.RegistryT (runRegistryT)
import           System.Metrics.Prometheus.Http.Scrape          (serveHttpTextMetricsT)
import           Types                                          (Config (Config, _authConfig))

instance GenerateList NoContent (Method -> Req NoContent) where
    generateList _ = []

type Web
     = "version" :> Get '[ PlainText, JSON] Text
       :<|> "api" :> (PA.API
                      :<|> Auth.API)
       :<|> Raw

liftedAuthServer :: Auth.GithubEndpoints -> Auth.Config -> Server Auth.API
liftedAuthServer githubEndpoints config =
    hoistServer (Proxy @Auth.API) liftAuthToHandler Auth.server
  where
    liftAuthToHandler ::
           ReaderT (Auth.GithubEndpoints, Auth.Config) (LoggingT (ExceptT ServerError IO)) a
        -> Handler a
    liftAuthToHandler =
        Handler . runStderrLoggingT . flip runReaderT (githubEndpoints, config)

server ::
       Server PA.API -> FilePath -> Auth.GithubEndpoints -> Config -> Server Web
server handlers _staticDir githubEndpoints Config {..} =
    version :<|> (handlers :<|> liftedAuthServer githubEndpoints _authConfig) :<|>
    serveDirectoryFileServer _staticDir

version :: Applicative m => m Text
version = pure gitRev

app :: Server PA.API
    -> FilePath
    -> Auth.GithubEndpoints
    -> Config
    -> Application
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
  handlers <- PS.mkHandlers
  appMonitor <- monitorEndpoints (Proxy @Web)
  logInfoN "Starting webserver."
  void . liftIO . forkIO . runSettings settings . appMonitor $ app handlers _staticDir githubEndpoints config
  serveHttpTextMetricsT 9091 ["metrics"]
