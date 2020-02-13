{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
module Cardano.Node.SimpleLog(
  -- $simpleLog
  SimpleLog
  , simpleLogDebug
  , simpleLogInfo
  , runSimpleLog
  ) where

import           Control.Monad.Freer        (Eff, LastMember, Member)
import qualified Control.Monad.Freer        as Eff
import           Control.Monad.Freer.State  (State)
import qualified Control.Monad.Freer.State  as Eff
import           Control.Monad.Freer.Writer (Writer)
import qualified Control.Monad.Freer.Writer as Eff
import           Control.Monad.IO.Class     (MonadIO, liftIO)
import           Control.Monad.Logger       (MonadLogger, logDebugN, logInfoN, runStdoutLoggingT)
import           Data.Text                  (Text)

-- $simpleLog
-- A @freer-simple@ wrapper around @Control.Monad.Logger@

data SimpleLog r where
    SimpleLogInfo :: Text -> SimpleLog ()
    SimpleLogDebug :: Text -> SimpleLog ()

simpleLogInfo :: Member SimpleLog effs => Text -> Eff effs ()
simpleLogInfo = Eff.send . SimpleLogInfo

simpleLogDebug :: Member SimpleLog effs => Text -> Eff effs ()
simpleLogDebug = Eff.send . SimpleLogDebug

runSimpleLog :: (MonadLogger m, MonadIO m) => Eff '[SimpleLog, m] a -> m a
runSimpleLog = Eff.runM . Eff.interpretM (\case
        SimpleLogInfo t -> runStdoutLoggingT $ logInfoN t
        SimpleLogDebug t -> runStdoutLoggingT $ logDebugN t)
