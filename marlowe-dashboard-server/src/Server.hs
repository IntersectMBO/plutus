{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Server where

import           API                         (API)
import           Control.Monad.Except        (ExceptT)
import           Control.Monad.IO.Class      (MonadIO, liftIO)
import           Control.Monad.Logger        (LoggingT, MonadLogger, logInfoN, runStderrLoggingT)
import           Control.Monad.Reader        (ReaderT, runReaderT)
import           Data.Aeson                  (FromJSON, ToJSON, eitherDecode, encode)
import           Data.Aeson                  as Aeson
import           Data.Proxy                  (Proxy (Proxy))
import           Data.String                 as S
import           Data.Text                   (Text)
import qualified Data.Text                   as Text
import           GHC.Generics                (Generic)
import           Network.Wai.Middleware.Cors (cors, corsRequestHeaders, simpleCorsResourcePolicy)
import           Servant                     (Application, Handler (Handler), Server, ServerError, hoistServer, serve,
                                              serveDirectoryFileServer, (:<|>) ((:<|>)), (:>))
import qualified WebSocket                   as WS

handlers :: FilePath -> Server API
handlers staticPath = WS.handle :<|> serveDirectoryFileServer staticPath

app :: FilePath -> Application
app staticPath =
  cors (const $ Just policy) $ serve (Proxy @API) (handlers staticPath)
  where
    policy =
      simpleCorsResourcePolicy

initializeApplication :: FilePath -> IO Application
initializeApplication staticPath = pure $ app staticPath
