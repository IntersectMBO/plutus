{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}

module Cardano.Node.SimpleLog(
    -- $simpleLog
    SimpleLog
    , simpleLogDebug
    , simpleLogInfo
    , runSimpleLog
    ) where

import           Control.Monad.Freer    (Eff, LastMember, Member, type (~>))
import qualified Control.Monad.Freer    as Eff
import           Control.Monad.IO.Class (MonadIO)
import           Control.Monad.Logger   (LogLevel (..), logWithoutLoc, runStdoutLoggingT)
import           Data.Text              (Text)

-- $simpleLog
-- A @freer-simple@ wrapper around @Control.Monad.Logger@
data SimpleLog r where
    SimpleLog :: LogLevel -> Text -> SimpleLog ()

simpleLogInfo :: Member SimpleLog effs => Text -> Eff effs ()
simpleLogInfo = Eff.send . SimpleLog LevelInfo

simpleLogDebug :: Member SimpleLog effs => Text -> Eff effs ()
simpleLogDebug = Eff.send . SimpleLog LevelDebug

runSimpleLog ::
       ( MonadIO m, LastMember m effs)
    => Eff (SimpleLog ': effs) ~> Eff effs
runSimpleLog =
    Eff.interpretM
        (\case
             SimpleLog level txt ->
                 runStdoutLoggingT $ logWithoutLoc "" level txt)
