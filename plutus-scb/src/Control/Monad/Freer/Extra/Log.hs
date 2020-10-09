{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}

module Control.Monad.Freer.Extra.Log(
    -- $log
    LogMsg
    , logDebug
    , logInfo
    , logWarn
    , runStderrLog
    , handleWriterLog
    ) where

import           Control.Monad.Freer     (Eff, LastMember, type (~>))
import qualified Control.Monad.Freer     as Eff
import           Control.Monad.Freer.Log (LogMessage (..), LogMsg (..), handleWriterLog, logDebug, logInfo, logWarn)
import qualified Control.Monad.Freer.Log as Log
import           Control.Monad.IO.Class  (MonadIO, liftIO)
import           Control.Monad.Logger    (LogLevel (..), logWithoutLoc, runStderrLoggingT)
import           Data.Text               (Text)

-- $log
-- A @freer-simple@ wrapper around @Control.Monad.Freer.Log.Log@

runStderrLog :: forall effs m. (LastMember m effs, MonadIO m) => Eff (LogMsg Text ': effs) ~> Eff effs
runStderrLog = Eff.interpretM $ \case
    LMessage es -> logMessage es

logMessage :: forall m. MonadIO m => LogMessage Text -> m ()
logMessage LogMessage{_logLevel, _logMessageContent} =
    let lvl = case _logLevel of
            Log.Debug     -> LevelDebug
            Log.Info      -> LevelInfo
            Log.Notice    -> LevelInfo
            Log.Warning   -> LevelWarn
            Log.Error     -> LevelError
            Log.Critical  -> LevelError
            Log.Alert     -> LevelError
            Log.Emergency -> LevelError
    in liftIO $ runStderrLoggingT $ logWithoutLoc "" lvl _logMessageContent
