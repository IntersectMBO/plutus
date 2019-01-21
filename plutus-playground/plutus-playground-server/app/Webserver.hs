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
import           Servant.Foreign                      (GenerateList, NoContent, Req, generateList)
import           Servant.Server                       (Server)
import           Types                                (Config (Config, _authConfig))

instance GenerateList NoContent (Method -> Req NoContent) where
  generateList _ = []

type Web
   = "version" :> Get '[ PlainText, JSON] Text
     :<|> "api" :> (PA.API
                    :<|> Auth.API)
     :<|> Raw

liftedAuthServer :: Auth.GithubEndpoints -> Auth.Config -> Server Auth.API
liftedAuthServer githubEndpoints config =
  hoistServer (Proxy @Auth.API) liftAuthToHandler $
  Auth.server githubEndpoints config
  where
    liftAuthToHandler :: LoggingT (ExceptT ServantErr IO) a -> Handler a
    liftAuthToHandler = Handler . runStderrLoggingT

server ::
     Server PA.API -> FilePath -> Auth.GithubEndpoints -> Config -> Server Web
server handlers _staticDir githubEndpoints Config {..} =
  version :<|> (handlers :<|> liftedAuthServer githubEndpoints _authConfig) :<|>
  serveDirectoryFileServer _staticDir

version :: Applicative m => m Text
version = pure $(gitHash)

app ::
     Server PA.API -> FilePath -> Auth.GithubEndpoints -> Config -> Application
app handlers _staticDir githubEndpoints config =
  gzip def . logStdout . cors (const $ Just policy) . serve (Proxy @Web) $
  server handlers _staticDir githubEndpoints config
  where
    policy =
      simpleCorsResourcePolicy
        {corsRequestHeaders = ["content-type", "set-cookie"]}

run :: (MonadLogger m, MonadIO m) => Settings -> FilePath -> Config -> m ()
run settings _staticDir config = do
  githubEndpoints <- liftIO Auth.mkGithubEndpoints
  handlers <- PS.mkHandlers
  logInfoN "Starting webserver."
  liftIO . runSettings settings $ app handlers _staticDir githubEndpoints config
