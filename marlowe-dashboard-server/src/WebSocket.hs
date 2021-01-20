{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}

module WebSocket where

import           Control.Monad.IO.Class        (MonadIO)
import           Data.Aeson                    (FromJSON)
import           Data.Aeson.Types              (ToJSON)
import           GHC.Generics                  (Generic)
import           Network.WebSockets.Connection (Connection, PendingConnection, withPingThread)
import           Servant                       (Handler)

handle :: MonadIO m => PendingConnection -> m ()
handle conn = pure ()

data StreamToServer
  = ServerMsg
  deriving (Show, Eq, Generic)
  deriving anyclass (FromJSON, ToJSON)

data StreamToClient
  = ClientMsg
  deriving (Show, Eq, Generic)
  deriving anyclass (FromJSON, ToJSON)
