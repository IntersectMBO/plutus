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
    , writeToLog
    , ignoreLog
    , traceLog
    ) where

import           Control.Monad.Freer
import           Control.Monad.Freer.Writer              (Writer (..), tell)
import           Data.Aeson                              (FromJSON, ToJSON)
import           Data.Foldable                           (traverse_)
import           Data.Text                               (Text)
import           Data.Text.Prettyprint.Doc
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
