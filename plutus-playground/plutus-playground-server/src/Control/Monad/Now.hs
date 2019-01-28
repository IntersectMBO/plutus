{-# LANGUAGE FlexibleInstances #-}

module Control.Monad.Now
  ( MonadNow
  , getCurrentTime
  , getPOSIXTime
  ) where

import           Control.Monad.Except      (ExceptT)
import           Control.Monad.Logger      (LoggingT)
import           Control.Monad.Trans.Class (lift)
import           Data.Time                 (UTCTime)
import qualified Data.Time                 as Time
import           Data.Time.Clock.POSIX     (POSIXTime)
import qualified Data.Time.Clock.POSIX     as Time

class Monad m =>
      MonadNow m
  where
  getCurrentTime :: m UTCTime
  getPOSIXTime :: m POSIXTime

instance MonadNow IO where
  getCurrentTime = Time.getCurrentTime
  getPOSIXTime = Time.getPOSIXTime

instance MonadNow m => MonadNow (ExceptT e m) where
  getCurrentTime = lift getCurrentTime
  getPOSIXTime = lift getPOSIXTime

instance MonadNow m => MonadNow (LoggingT m) where
  getCurrentTime = lift getCurrentTime
  getPOSIXTime = lift getPOSIXTime
