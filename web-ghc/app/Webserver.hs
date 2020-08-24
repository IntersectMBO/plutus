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
{-# OPTIONS_GHC -Wno-orphans #-}

module Webserver
  ( run,
  )
where

import           Control.Concurrent                             (forkIO)
import           Control.Monad                                  (void)
import           Control.Monad.Catch                            (MonadMask)
import           Control.Monad.Except                           (runExceptT)
import           Control.Monad.IO.Class                         (MonadIO, liftIO)
import           Control.Monad.Logger                           (MonadLogger, logInfoN)
import           Data.Default.Class                             (def)
import           Data.Proxy                                     (Proxy (Proxy))
import           Data.Text                                      (Text)
import           Git                                            (gitRev)
import           Interpreter                                    (compile, maxInterpretationTime)
import           Language.Haskell.Interpreter                   (InterpreterError, InterpreterResult)
import           Language.Haskell.Interpreter                   (SourceCode (SourceCode))
import           Network.Wai                                    (Application)
import           Network.Wai.Handler.Warp                       (Settings, runSettings)
import           Network.Wai.Middleware.Cors                    (cors, corsRequestHeaders, simpleCorsResourcePolicy)
import           Network.Wai.Middleware.Gzip                    (gzip)
import           Network.Wai.Middleware.RequestLogger           (logStdout)
import           Servant                                        ((:<|>) ((:<|>)), (:>), Get, JSON, PlainText, Post,
                                                                 ReqBody, serve)
import           Servant.Prometheus                             (monitorEndpoints)
import           Servant.Server                                 (Server)
import           System.Metrics.Prometheus.Concurrent.RegistryT (runRegistryT)
import           System.Metrics.Prometheus.Http.Scrape          (serveHttpTextMetricsT)

type API =
  "version" :> Get '[PlainText, JSON] Text
    :<|> "health" :> Get '[JSON] ()
    :<|> "runghc" :> ReqBody '[PlainText] Text :> Post '[JSON] (Either InterpreterError (InterpreterResult String))

server :: Server API
server =
  version :<|> health :<|> runghc

version :: Applicative m => m Text
version = pure gitRev

health :: Applicative m => m ()
health = pure ()

runghc ::
  MonadMask m =>
  MonadIO m =>
  Text ->
  m (Either InterpreterError (InterpreterResult String))
runghc code = do
  liftIO $ print code
  runExceptT $ compile maxInterpretationTime $ SourceCode code

app :: Application
app =
  gzip def . logStdout . cors (const $ Just policy) . serve (Proxy @API) $ server
  where
    policy =
      simpleCorsResourcePolicy
        { corsRequestHeaders = ["content-type", "set-cookie"]
        }

run :: (MonadLogger m, MonadIO m) => Settings -> m ()
run settings = runRegistryT $ do
  appMonitor <- monitorEndpoints (Proxy @API)
  logInfoN "Starting webserver."
  void . liftIO . forkIO . runSettings settings . appMonitor $ app
  serveHttpTextMetricsT 9091 ["metrics"]
