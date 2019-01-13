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
{-# OPTIONS_GHC   -Wno-orphans #-}

module Webserver
  ( run
  ) where

import           Control.Monad.IO.Class               (MonadIO, liftIO)
import           Control.Monad.Logger                 (MonadLogger, logInfoN)
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
import           Servant                              ((:<|>) ((:<|>)), (:>), Get, JSON, PlainText, Raw, serve,
                                                       serveDirectoryFileServer)
import           Servant.Foreign                      (GenerateList, NoContent, Req, generateList)
import           Servant.Server                       (Server)

instance GenerateList NoContent (Method -> Req NoContent) where
  generateList _ = []

type Web
   = "version" :> Get '[ PlainText, JSON] Text :<|> "api" :> PA.API :<|> Raw

server :: Server PA.API -> FilePath -> Server Web
server handlers staticDir = version :<|> handlers :<|> serveDirectoryFileServer staticDir

version :: Applicative m => m Text
version = pure $(gitHash)

app :: Server PA.API -> FilePath -> Application
app handlers staticDir =
  gzip def . logStdout . cors (const $ Just policy) . serve webApi $
  server handlers staticDir
  where
    policy = simpleCorsResourcePolicy {corsRequestHeaders = ["content-type"]}
    webApi :: Proxy Web
    webApi = Proxy

run :: (MonadLogger m, MonadIO m) => Settings -> FilePath -> m ()
run settings staticDir = do
  handlers <- PS.mkHandlers
  logInfoN "Starting webserver."
  liftIO . runSettings settings $ app handlers staticDir
