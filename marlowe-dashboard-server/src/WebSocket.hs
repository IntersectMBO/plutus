module WebSocket where

import           Control.Monad.IO.Class        (MonadIO)
import           Network.WebSockets.Connection (Connection, PendingConnection, withPingThread)
import           Servant                       (Handler)

handle :: MonadIO m => PendingConnection -> m ()
handle conn = pure ()
