{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE ScopedTypeVariables #-}

module WebSocket where

import           Control.Monad                 (forever)
import           Control.Monad.IO.Class        (MonadIO (liftIO))
import           Data.Aeson                    (FromJSON)
import qualified Data.Aeson                    as JSON
import           Data.Aeson.Types              (ToJSON)
import           Data.UUID                     (UUID)
import           Data.UUID.V4                  (nextRandom)
import           GHC.Generics                  (Generic)
import qualified Network.WebSockets            as WS
import           Network.WebSockets.Connection (Connection, PendingConnection, receiveData, withPingThread)
import           Servant                       (Handler)

handle :: MonadIO m => PendingConnection -> m ()
handle pending = liftIO $ do
  connection <- WS.acceptRequest pending
  uuid <- nextRandom
  putStrLn "received ws connection"
  withPingThread connection 30 (pure ()) $ handleRequest connection uuid

handleRequest :: Connection -> UUID -> IO ()
handleRequest connection uuid = forever $ do
  msg <- receiveData connection
  print msg
  v <- case JSON.eitherDecode msg of
    Left e -> do
      putStrLn e
      pure False
    Right (ServerMsg v) -> pure v
  let resp = JSON.encode (ClientMsg (not v))
  WS.sendTextData connection resp

newtype StreamToServer
  = ServerMsg Bool
  deriving (Show, Eq, Generic)
  deriving anyclass (FromJSON, ToJSON)

newtype StreamToClient
  = ClientMsg Bool
  deriving (Show, Eq, Generic)
  deriving anyclass (FromJSON, ToJSON)
