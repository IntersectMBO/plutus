{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Control.Concurrent.ServiceAvailability where

import           Control.Concurrent (MVar, putMVar, takeMVar)

-- | A semaphore-like construct whereby a service can signal to
-- another thread that it's finished its startup phase, and is now
-- available to use.
class ServiceAvailability m a where
  available :: a -> m ()
  starting :: a -> m ()

instance ServiceAvailability IO (MVar ()) where
  available mvar = putMVar mvar ()
  starting = takeMVar
