module Control.Concurrent.Availability
    ( Availability
    , newToken
    , starting
    , available
    ) where

import           Control.Concurrent     (MVar, newEmptyMVar, putMVar, takeMVar)
import           Control.Monad.IO.Class (MonadIO, liftIO)

-- | A semaphore-like construct whereby a service can signal to
-- another thread that it's finished its startup phase, and is now
-- available to use.
newtype Availability =
    Availability (MVar ())

newToken :: MonadIO m => m Availability
newToken = Availability <$> liftIO newEmptyMVar

starting :: MonadIO m => Availability -> m ()
starting (Availability mvar) = liftIO $ takeMVar mvar

available :: MonadIO m => Availability -> m ()
available (Availability mvar) = liftIO $ putMVar mvar ()
