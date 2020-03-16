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
    , logWarn
    , runStderrLog
    , writeToLog
    ) where

import           Control.Monad.Freer                   (Eff, LastMember, Member, type (~>))
import qualified Control.Monad.Freer                   as Eff
import           Control.Monad.Freer.Writer            (Writer (..))
import           Control.Monad.IO.Class                (MonadIO, liftIO)
import           Control.Monad.Logger                  (LogLevel (..), logWithoutLoc, runStderrLoggingT)
import           Data.Foldable                         (traverse_)
import           Data.Text                             (Text)
import           Data.Text.Prettyprint.Doc             (Pretty (..), defaultLayoutOptions, layoutPretty)
import qualified Data.Text.Prettyprint.Doc.Render.Text as Render

-- $log
-- A @freer-simple@ wrapper around @Control.Monad.Logger@
data Log r where
    Log :: LogLevel -> Text -> Log ()

logInfo :: Member Log effs => Text -> Eff effs ()
logInfo = Eff.send . Log LevelInfo

logDebug :: Member Log effs => Text -> Eff effs ()
logDebug = Eff.send . Log LevelDebug

logWarn :: Member Log effs => Text -> Eff effs ()
logWarn = Eff.send . Log LevelWarn

runStderrLog :: (LastMember m effs, MonadIO m) => Eff (Log ': effs) ~> Eff effs
runStderrLog =
    Eff.interpretM
        (\case
             Log level txt -> liftIO $ runStderrLoggingT $ logWithoutLoc "" level txt)

-- | Re-interpret a 'Writer' effect by writing the events to the log
writeToLog ::
    ( Member Log effs
    , Pretty e
    , Traversable f
    )
    => Eff (Writer (f e) ': effs)
    ~> Eff effs
writeToLog = Eff.interpret $ \case
    Tell es -> traverse_ (logInfo . Render.renderStrict . layoutPretty defaultLayoutOptions  .  pretty) es
