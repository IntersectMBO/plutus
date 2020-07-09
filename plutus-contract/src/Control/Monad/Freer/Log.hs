{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StrictData #-}
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
    , LogMsg
    , LogObserve
    , LogLevel(..)
    , LogMessage(..)
    , logLevel
    , logMessageContent
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
    , logToWriter
    , observeAsLogMessage
    , transformLogMessages
    , renderLogMessages
    ) where

import Control.Lens (Prism', review, makeLenses)
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

type Log = LogMsg Text

data LogMsg a r where
    LMessage :: LogMessage a -> LogMsg a ()

data LogObserve effs r where
    LObserve :: LogLevel -> Text -> Eff effs b -> LogObserve effs b

-- | The severity level of a log message
--   See https://en.wikipedia.org/wiki/Syslog#Severity_level
data LogLevel =
        Debug
        | Info
        | Notice
        | Warning
        | Error
        | Critical
        | Alert
        | Emergency
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty LogLevel where
    pretty = \case
        Debug      -> "[DEBUG]"
        Info       -> "[INFO]"
        Notice     -> "[NOTICE]"
        Warning    -> "[WARNING]"
        Error      -> "[ERROR]"
        Critical   -> "[CRITICAL]"
        Alert      -> "[ALERT]"
        Emergency  -> "[EMERGENCY]"

data LogMessage a = LogMessage { _logLevel :: LogLevel, _logMessageContent :: a }
    deriving stock (Show, Eq, Ord, Generic, Functor, Foldable, Traversable)
    deriving anyclass (ToJSON, FromJSON)

makeLenses ''LogMessage

instance Pretty a => Pretty (LogMessage a) where
    pretty LogMessage{_logLevel, _logMessageContent} =
        pretty _logLevel <+> pretty _logMessageContent

logDebug :: forall a effs. Member (LogMsg a) effs => a -> Eff effs ()
logDebug m = send $ LMessage (LogMessage Debug m)

logWarn :: forall a effs. Member (LogMsg a) effs => a -> Eff effs ()
logWarn m = send $ LMessage (LogMessage Warning m)

logInfo :: forall a effs. Member (LogMsg a) effs => a -> Eff effs ()
logInfo m = send $ LMessage (LogMessage Info m)

-- | Write a log message before and after an action.
surround :: Member (LogObserve effs) effs => LogLevel -> Text -> Eff effs a -> Eff effs a
surround lvl txt action = 
    send $ LObserve lvl txt action

-- | @surroundInfo = surround Info@
surroundInfo :: Member (LogObserve effs) effs => Text -> Eff effs a -> Eff effs a
surroundInfo = surround Info

-- | @surroundDebug = surround Debug@
surroundDebug :: Member (LogObserve effs) effs => Text -> Eff effs a -> Eff effs a
surroundDebug = surround Debug

-- | @surroundWarn = surround Warn@
surroundWarn :: Member (LogObserve effs) effs => Text -> Eff effs a -> Eff effs a
surroundWarn = surround Warning

transformLogMessages ::
    forall a b effs.
    (a -> b)
    -> Eff (LogMsg a ': effs)
    ~> Eff (LogMsg b ': effs)
transformLogMessages f =
    reinterpret @(LogMsg a) @(LogMsg b) $ \case
        LMessage lms -> send (LMessage $ fmap f lms)

renderLogMessages ::
    forall a effs.
    Pretty a
    => Eff (LogMsg a ': effs)
    ~> Eff (LogMsg Text ': effs)
renderLogMessages = 
    transformLogMessages (Render.renderStrict . layoutPretty defaultLayoutOptions . pretty)

-- | Re-interpret a 'Writer' effect by writing the events to the log
writeToLog ::
    forall a f effs.
    ( Member (LogMsg a) effs
    , Traversable f
    )
    => Eff (Writer (f a) ': effs)
    ~> Eff effs
writeToLog = interpret $ \case
    Tell es -> traverse_ (logInfo @a) es

-- | Re-interpret a 'Log' effect with a 'Writer'
logToWriter ::
    forall a w effs.
    ( Member (Writer w) effs
    )
    => Prism' w (LogMessage a)
    -> LogMsg a
    ~> Eff effs
logToWriter p = \case
    LMessage msg -> tell @w (review p msg)

-- | Ignore all log messages.
ignoreLog :: Eff (LogMsg a ': effs) ~> Eff effs
ignoreLog = interpret $ \case
    LMessage _ -> pure ()

-- | Interpret the 'LogObserve' effect by logging a "start" message
--   before the action and an "end" message after the action.
observeAsLogMessage ::
    forall effs.
    Member (LogMsg Text) effs
    => Eff ((LogObserve effs) ': effs)
    ~> Eff effs
observeAsLogMessage = interpret $ \case
    LObserve lvl txt action -> do
        send (LMessage $ LogMessage lvl $ txt <> " start")
        a <- action
        send (LMessage $ LogMessage lvl $ txt <> " end")
        pure a

-- | Write the log to stdout using 'Debug.Trace.trace'
traceLog :: Eff (LogMsg String ': effs) ~> Eff effs
traceLog = interpret $ \case
    LMessage msg -> Trace.trace (Render.renderString . layoutPretty defaultLayoutOptions . pretty $ msg) (pure ())
