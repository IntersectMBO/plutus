{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TypeOperators      #-}

module Control.Monad.Freer.Log(
    Log
    , LogLevel(..)
    , LogMessage(..)
    , logDebug
    , logWarn
    , logInfo
    , surround
    , surroundDebug
    , surroundInfo
    , surroundWarn
    -- * Handlers
    , writeToLog
    , ignoreLog
    , traceLog
    ) where

import           Control.Monad.Freer
import           Control.Monad.Freer.Writer              (Writer (..), tell)
import           Data.Aeson                              (FromJSON, ToJSON)
import           Data.Foldable                           (traverse_)
import           Data.Text                               (Text)
import           Data.Text.Prettyprint.Doc               hiding (surround)
import qualified Data.Text.Prettyprint.Doc.Render.String as Render
import qualified Data.Text.Prettyprint.Doc.Render.Text   as Render
import qualified Debug.Trace                             as Trace
import           GHC.Generics                            (Generic)

type Log = Writer [LogMessage]

data LogLevel = Debug | Info | Warn
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (ToJSON, FromJSON)

data LogMessage = LogMessage { logLevel :: LogLevel, logMessageText :: Text }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty LogLevel where
    pretty = \case
        Debug -> "[DEBUG]"
        Info ->  "[INFO ]"
        Warn ->  "[WARN ]"

instance Pretty LogMessage where
    pretty LogMessage{logLevel, logMessageText} =
        pretty logLevel <+> pretty logMessageText

logDebug :: Member Log effs => Text -> Eff effs ()
logDebug m = tell [LogMessage Debug m]

logWarn :: Member Log effs => Text -> Eff effs ()
logWarn m = tell [LogMessage Warn m]

logInfo :: Member Log effs => Text -> Eff effs ()
logInfo m = tell [LogMessage Info m]

-- | Write a log message before and after an action.
surround :: Member Log effs => LogLevel -> Text -> Eff effs a -> Eff effs a
surround lvl txt action = do
    tell [LogMessage lvl (txt <> " start")]
    result <- action
    tell [LogMessage lvl (txt <> " end")]
    pure result

-- | @surroundInfo = surround Info@
surroundInfo :: Member Log effs => Text -> Eff effs a -> Eff effs a
surroundInfo = surround Info

-- | @surroundDebug = surround Debug@
surroundDebug :: Member Log effs => Text -> Eff effs a -> Eff effs a
surroundDebug = surround Debug

-- | @surroundWarn = surround Warn@
surroundWarn :: Member Log effs => Text -> Eff effs a -> Eff effs a
surroundWarn = surround Warn

-- | Re-interpret a 'Writer' effect by writing the events to the log
writeToLog ::
    ( Member Log effs
    , Pretty e
    , Traversable f
    )
    => Eff (Writer (f e) ': effs)
    ~> Eff effs
writeToLog = interpret $ \case
    Tell es -> traverse_ (logInfo . Render.renderStrict . layoutPretty defaultLayoutOptions . pretty) es

-- | Ignore all log messages.
ignoreLog :: Eff (Log ': effs) ~> Eff effs
ignoreLog = interpret $ \case
    Tell _ -> pure ()

-- | Write the log to stdout using 'Debug.Trace.trace'
traceLog :: Eff (Log ': effs) ~> Eff effs
traceLog = interpret $ \case
    Tell msg -> Trace.trace (Render.renderString . layoutPretty defaultLayoutOptions . pretty $ msg) (pure ())
