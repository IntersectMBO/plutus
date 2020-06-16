{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}

module Control.Monad.Freer.Extra.Log(
    -- $log
      Log
    , logDebug
    , logInfo
    , logWarn
    , runStderrLog
    , writeToLog
    ) where

import           Control.Monad.Freer        (Eff, LastMember, type (~>))
import qualified Control.Monad.Freer        as Eff
import           Control.Monad.Freer.Log    (Log, LogMessage (..), logDebug, logInfo, logWarn, writeToLog)
import qualified Control.Monad.Freer.Log    as Log
import           Control.Monad.Freer.Writer (Writer (..))
import           Control.Monad.IO.Class     (MonadIO, liftIO)
import           Control.Monad.Logger       (LogLevel (..), logWithoutLoc, runStderrLoggingT)
import           Data.Foldable              (traverse_)

-- $log
-- A @freer-simple@ wrapper around @Control.Monad.Freer.Log.Log@

runStderrLog :: (LastMember m effs, MonadIO m) => Eff (Log ': effs) ~> Eff effs
runStderrLog = Eff.interpretM $ \case
    Tell es -> traverse_ logMessage es

logMessage :: MonadIO m => LogMessage -> m ()
logMessage LogMessage{logLevel, logMessageText} =
    let lvl = case logLevel of
            Log.Debug -> LevelDebug
            Log.Info  -> LevelInfo
            Log.Warn  -> LevelWarn
    in liftIO $ runStderrLoggingT $ logWithoutLoc "" lvl logMessageText
