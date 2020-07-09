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
    , logMessage
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
    , handleObserve
    ) where

import Control.Lens (Prism', review, makeLenses, prism')
import           Control.Monad.Freer
import Control.Monad.Freer.Extras (raiseUnder)
import Control.Monad.Freer.State (State, modify, evalState, get, put)
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

data LogObserve r where
    LObserveBefore :: LogLevel -> Text -> LogObserve ()
    LObserveAfter  :: LogObserve ()

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

logMessage :: LogLevel -> Prism' (LogMessage a) a
logMessage lvl = prism' (LogMessage lvl) (\case { LogMessage lvl' a | lvl' == lvl -> Just a; _ -> Nothing})

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
surround :: Member LogObserve effs => LogLevel -> Text -> Eff effs a -> Eff effs a
surround lvl txt action = do
    send $ LObserveBefore lvl txt
    a <- action
    send LObserveAfter
    pure a

-- | @surroundInfo = surround Info@
surroundInfo :: Member LogObserve effs => Text -> Eff effs a -> Eff effs a
surroundInfo = surround Info

-- | @surroundDebug = surround Debug@
surroundDebug :: Member LogObserve effs => Text -> Eff effs a -> Eff effs a
surroundDebug = surround Debug

-- | @surroundWarn = surround Warn@
surroundWarn :: Member LogObserve effs => Text -> Eff effs a -> Eff effs a
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

data Observation s =
    Observation
        { obsLabel :: Text
        , obsStart :: s
        , obsEnd :: s
        }

-- | Handle the 'LogObserve' effect by recording observations
--   @s@ before and after the observed action, and turning
--   them into 'LogMessage (Observation s)' values.
handleObserve ::
    forall s effs.
    Eff effs s -- ^ How to get the current 's'
    -> (LogMessage (Observation s) -> Eff effs ()) -- what to do with the observation
    -> Eff (LogObserve ': effs)
    ~> Eff effs
handleObserve getCurrent handleObs = 
    evalState @[LogMessage (Text, s)] []
    . hdl
    . raiseUnder @effs @LogObserve @(State [LogMessage (Text, s)])
    where 
        hdl = interpret $ \case
            LObserveBefore lvl label -> do
                current <- raise getCurrent
                let msg = review (logMessage lvl) (label, current)
                modify @[LogMessage (Text, s)] (msg :)
            LObserveAfter -> do
                current <- raise getCurrent
                observations <- get
                case observations of
                    (x:xs) -> do
                        let x' = fmap (\(lbl, start) -> Observation{obsLabel=lbl,obsStart=start,obsEnd=current}) x
                        raise $ handleObs x'
                        put xs
                    _ -> error "handleObserve: Corrupted state" -- FIXME

-- | Interpret the 'LogObserve' effect by logging a "start" message
--   before the action and an "end" message after the action.
observeAsLogMessage ::
    forall effs.
    Member (LogMsg Text) effs
    => Eff (LogObserve ': effs)
    ~> Eff effs
observeAsLogMessage = 
    evalState @[LogMessage Text] []
    . hdl
    . raiseUnder @effs @LogObserve @(State [LogMessage Text])
    where
        hdl = interpret $ \case
            LObserveBefore lvl label -> do
                let msg = LogMessage lvl label
                raise @effs $ send $ LMessage $ fmap (<> " start") msg
                modify (msg :)
            LObserveAfter -> do
                observations <- get @[LogMessage Text]
                case observations of
                    (x:xs) -> do
                        send $ LMessage $ fmap (<> " end") x
                        put xs
                    _ -> error "observeAsLogMessage: Corrupted state" -- FIXME

-- | Write the log to stdout using 'Debug.Trace.trace'
traceLog :: Eff (LogMsg String ': effs) ~> Eff effs
traceLog = interpret $ \case
    LMessage msg -> Trace.trace (Render.renderString . layoutPretty defaultLayoutOptions . pretty $ msg) (pure ())
