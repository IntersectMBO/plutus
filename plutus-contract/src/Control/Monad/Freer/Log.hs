{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE StrictData         #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeOperators      #-}

module Control.Monad.Freer.Log(
    -- $log
    -- * Logging
    LogMsg(..)
    , LogLevel(..)
    , LogMessage(..)
    , logLevel
    , logMessageContent
    , logMessage
    , logDebug
    , logWarn
    , logInfo
    -- ** Handlers
    , contramapLog
    , writeToLog
    , ignoreLog
    , traceLog
    , logToWriter
    , renderLogMessages
    -- * Tracing
    , LogObserve(..)
    , surround
    , surroundDebug
    , surroundInfo
    , surroundWarn
    -- ** Handlers
    , observeAsLogMessage
    , handleObserve
    ) where

import           Control.Lens                            (Prism', makeLenses, prism', review)
import           Control.Monad.Freer
import           Control.Monad.Freer.Extras              (raiseUnder)
import           Control.Monad.Freer.State               (State, get, put, runState)
import           Control.Monad.Freer.Writer              (Writer (..), tell)
import           Data.Aeson                              (FromJSON, ToJSON)
import           Data.Foldable                           (traverse_)
import           Data.Text                               (Text)
import           Data.Text.Prettyprint.Doc               hiding (surround)
import qualified Data.Text.Prettyprint.Doc.Render.String as Render
import qualified Data.Text.Prettyprint.Doc.Render.Text   as Render
import qualified Debug.Trace                             as Trace
import           GHC.Generics                            (Generic)

-- $log
-- This module provides effects and handlers for structured logging and
-- tracing.

{- Note [Logging and Tracing]

This module provides two effects for structured logging, implementing a
'freer-simple' version of https://github.com/input-output-hk/iohk-monitoring-framework/tree/master/contra-tracer.

* 'LogMsg' and its handlers correspond to 'Control.Tracer'
* 'LogObserve' and its handler correspond to 'Control.Tracer.Observe'

= LogMsg

When using 'Control.Tracer' with mtl-style effects, we usually have a
'Tracer m s' at the top level with a sum type @s@, and we can use
'contramap' to get tracers for the finer-grained message
types.

In this module we have 'Member (LogMsg s) effs' instead of the 'Tracer m s'
value. With 'freer' effects we can have many instances of 'LogMsg' in our
effects stack so we don't need to call 'contramap' or similar on
the client side. The conversion to @s@ happens in the big effect handler that
discharges all the 'LogMsg' effects.

= LogObserve

'LogObserve' is an effect for taking measurements before and after an action,
and recording the difference between them. It is implemented using two markers,
'LObserveBefore' and 'LObserveAfter'.

Some effects such as Error, Prompt may short-circuit the action, so that the
LObserveAfter marker is never encountered by the handler. 'handleObserve' deals
with this by keeping a stack of unmatched 'LObserveBefore' markers and popping 
as many items of the stack as needed whenever 'LObserveAfter' is run. It works 
even if the topmost LObserveAfter is never seen, by popping all remaining items 
off the stack at the end.

-}

data LogMsg a r where
    LMessage :: LogMessage a -> LogMsg a ()

data LogObserve r where
    LObserveBefore :: LogLevel -> Text -> LogObserve Integer
    LObserveAfter  :: Integer -> LogObserve ()

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

-- | Re-interpret a logging effect by mapping the
--   log messages.
contramapLog ::
    forall a b c effs.
    Member (LogMsg a) effs
    => (b -> a)
    -> Eff (LogMsg b ': effs) c
    -> Eff effs c
contramapLog f = interpret $ \case
    LMessage msg -> send $ LMessage (fmap f msg)

-- | Pretty-print the log messages
renderLogMessages ::
    forall a effs.
    ( Member (LogMsg Text) effs
    , Pretty a
    )
    => Eff (LogMsg a ': effs)
    ~> Eff effs
renderLogMessages =
    contramapLog (Render.renderStrict . layoutPretty defaultLayoutOptions . pretty)

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

-- | Write the log to stdout using 'Debug.Trace.trace'
traceLog :: Eff (LogMsg String ': effs) ~> Eff effs
traceLog = interpret $ \case
    LMessage msg -> Trace.trace (Render.renderString . layoutPretty defaultLayoutOptions . pretty $ msg) (pure ())

-- | Write a log message before and after an action.
surround :: Member LogObserve effs => LogLevel -> Text -> Eff effs a -> Eff effs a
surround lvl txt action = do
    i <- send $ LObserveBefore lvl txt
    a <- action
    send $ LObserveAfter i
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

-- | How did the observed action end
data ExitMode =
    Regular -- ^ The action was run to completion
    | Irregular -- ^ Execution of the observed action was cut short. This can happen if you use 'LogObserve' in combination with 'Error', 'NonDet', 'Prompt' or similar effects.
    deriving (Eq, Ord, Show)

-- | An observation with measurements before and after running an action.
data Observation s =
    Observation
        { obsLabel :: Text -- ^ Description of the action
        , obsStart :: s -- ^ Measurement before running the action
        , obsEnd   :: s -- ^ Measurement after running the action
        , obsExit  :: ExitMode -- ^ 'ExitMode' of the action.
        }

--  | An 'Observation' that doesn't have an 'obsEnd' value yet.
data PartialObservation s =
    PartialObservation
        { obsMsg   :: LogMessage Text
        , obsValue :: s
        , obsDepth :: Integer
        }

-- | State of partial observations
data ObsState s =
    ObsState
        { obsMaxDepth :: Integer
        , obsPartials :: [PartialObservation s]
        }

initialState :: ObsState s
initialState = ObsState 0 []

-- see note [Logging and Tracing]
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
    handleFinalState
    . runState @(ObsState s) initialState
    . hdl
    . raiseUnder @effs @LogObserve @(State (ObsState s))
    where
        -- empty the stack of partial observations at the very end.
        handleFinalState action = do
            (result, finalState) <- action
            _ <- handleObserveAfter finalState 0
            pure result

        -- when an action with the given depth is finished, take the final
        -- measurement and clear the stack of partial observations.
        handleObserveAfter :: ObsState s -> Integer -> Eff effs (ObsState s)
        handleObserveAfter ObsState{obsPartials} i = do
                current <- getCurrent
                let (finishedPartials, remainingPartials) = span ((<=) i . obsDepth) obsPartials
                flip traverse_ finishedPartials $ \PartialObservation{obsMsg, obsValue,obsDepth} -> do
                    let exitMode = if obsDepth == i then Regular else Irregular
                        message  = fmap (\l -> Observation{obsLabel=l, obsStart=obsValue, obsEnd=current, obsExit=exitMode}) obsMsg
                    handleObs message
                pure ObsState{obsMaxDepth=i - 1, obsPartials=remainingPartials}

        hdl = interpret $ \case
            LObserveBefore lvl label -> do
                current <- raise getCurrent
                ObsState{obsMaxDepth, obsPartials} <- get
                let newMaxDepth = obsMaxDepth + 1
                    msg = PartialObservation
                            { obsMsg = LogMessage lvl label
                            , obsValue = current
                            , obsDepth = newMaxDepth
                            }
                put ObsState{obsMaxDepth=newMaxDepth,obsPartials=msg:obsPartials}
                pure newMaxDepth
            LObserveAfter i -> do
                currentState <- get @(ObsState s)
                newState <- raise (handleObserveAfter currentState i)
                put newState

-- | Interpret the 'LogObserve' effect by logging a "start" message
--   before the action and an "end" message after the action.
observeAsLogMessage ::
    forall effs.
    Member (LogMsg Text) effs
    => Eff (LogObserve ': effs)
    ~> Eff effs
observeAsLogMessage =
    handleObserve (pure ()) handleAfter
    . interpose handleBefore
        where
            handleBefore :: LogObserve ~> Eff (LogObserve ': effs)
            handleBefore = \case
                    LObserveBefore lvl label -> do
                        let msg = LogMessage{_logLevel=lvl, _logMessageContent=label <> " start"}
                        send $ LMessage msg
                        send $ LObserveBefore lvl label
                    LObserveAfter i -> send $ LObserveAfter i
            handleAfter msg = do
                let msg' = fmap (\Observation{obsLabel, obsExit} -> case obsExit of { Regular -> obsLabel <> " end"; Irregular -> obsLabel <> " end (irregular)"} ) msg
                send $ LMessage msg'
