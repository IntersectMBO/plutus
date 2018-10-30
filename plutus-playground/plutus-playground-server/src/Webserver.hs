{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeOperators              #-}

module Webserver
  ( run
  ) where

import           Control.Monad.IO.Class                 (MonadIO, liftIO)
import           Control.Monad.Logger                   (LoggingT, MonadLogger, runStderrLoggingT)
import           Data.Default.Class                     (def)
import           Data.Proxy                             (Proxy (Proxy))
import           Data.Text                              (Text)
import           Development.GitRev                     (gitHash)
import           Network.HTTP.Types                     (Method)
import           Network.Wai                            (Application)
import           Network.Wai.Handler.Warp               (Settings, runSettings)
import           Network.Wai.Middleware.Cors            (cors, corsRequestHeaders, simpleCorsResourcePolicy)
import           Network.Wai.Middleware.Gzip            (gzip)
import           Network.Wai.Middleware.RequestLogger   (logStdout)
import           Network.Wai.Middleware.Servant.Options (provideOptions)
import qualified Playground.API                         as PA
import qualified Playground.Server                      as PS
import           Servant                                ((:<|>) ((:<|>)), (:>), Get, JSON, PlainText, Post, Raw,
                                                         ReqBody, serve, serveDirectoryFileServer)
import           Servant.Foreign                        (GenerateList, NoContent, Req, generateList)
import           Servant.Server                         (Handler, Server)

instance GenerateList NoContent (Method -> Req NoContent) where
  generateList _ = []

type Web
   = "version" :> Get '[ PlainText, JSON] Text :<|> "api" :> PA.API :<|> Raw

server :: FilePath -> Server Web
server staticDir =
  version :<|> PS.handlers :<|> serveDirectoryFileServer staticDir

version :: Applicative m => m Text
version = pure $(gitHash)

app :: FilePath -> Application
app staticDir =
  gzip def . logStdout . cors (const $ Just policy) . serve webApi $
  server staticDir
  where
    policy = simpleCorsResourcePolicy {corsRequestHeaders = ["content-type"]}
    webApi :: Proxy Web
    webApi = Proxy

run :: (MonadLogger m, MonadIO m) => Settings -> FilePath -> m ()
run settings staticDir = liftIO . runSettings settings $ app staticDir
