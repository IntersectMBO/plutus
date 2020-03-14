{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}

module Control.Monad.Freer.Extra.Log(
    -- $log
      Log(..)
    , logDebug
    , logInfo
    , runStderrLog
    ) where

import           Control.Monad.Freer  (Eff, LastMember, Member, type (~>))
import qualified Control.Monad.Freer  as Eff
import           Control.Monad.Logger (LogLevel (..), logWithoutLoc, runStderrLoggingT)
import           Data.Text            (Text)

-- $log
-- A @freer-simple@ wrapper around @Control.Monad.Logger@
data Log r where
    Log :: LogLevel -> Text -> Log ()

logInfo :: Member Log effs => Text -> Eff effs ()
logInfo = Eff.send . Log LevelInfo

logDebug :: Member Log effs => Text -> Eff effs ()
logDebug = Eff.send . Log LevelDebug

runStderrLog :: (LastMember IO effs) => Eff (Log ': effs) ~> Eff effs
runStderrLog =
    Eff.interpretM
        (\case
             Log level txt -> runStderrLoggingT $ logWithoutLoc "" level txt)
