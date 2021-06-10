{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Webserver
  ( run,
  )
where

import           Control.Concurrent                             (forkIO)
import           Control.Monad                                  (void)
import           Control.Monad.IO.Class                         (MonadIO, liftIO)
import           Control.Monad.Logger                           (MonadLogger, logInfoN)
import           Data.Default.Class                             (def)
import           Data.Proxy                                     (Proxy (Proxy))
import           Data.Time.Units                                (Second, TimeUnit, convertUnit)
import           Network.Wai                                    (Application)
import           Network.Wai.Handler.Warp                       (Settings, runSettings)
import           Network.Wai.Middleware.Cors                    (cors, corsRequestHeaders, simpleCorsResourcePolicy)
import           Network.Wai.Middleware.Gzip                    (gzip)
import           Network.Wai.Middleware.RequestLogger           (logStdout)
import           Servant                                        (serve)
import           Servant.Prometheus                             (monitorEndpoints)
import           System.Metrics.Prometheus.Concurrent.RegistryT (runRegistryT)
import           System.Metrics.Prometheus.Http.Scrape          (serveMetricsT)
import           Webghc.Server                                  (API, server)


app :: Second -> Application
app timeOutSecs =
  gzip def . logStdout . cors (const $ Just policy) . serve (Proxy @API) $ server timeOutSecs
  where
    policy =
      simpleCorsResourcePolicy
        { corsRequestHeaders = ["content-type", "set-cookie"]
        }

run :: (MonadLogger m, TimeUnit t, MonadIO m) => Settings -> t -> m ()
run settings timeOutSecs = runRegistryT $ do
  appMonitor <- monitorEndpoints (Proxy @API)
  logInfoN "Starting webserver."
  void . liftIO . forkIO . runSettings settings . appMonitor $ app (convertUnit timeOutSecs)
  serveMetricsT 9091 ["metrics"]
