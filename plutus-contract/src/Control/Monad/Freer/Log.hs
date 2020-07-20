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
    , logInfo
    , logWarn
    , logError
    -- ** Handlers
    , mapLog
    , handleWriterLog
    , handleLogIgnore
    , handleLogTrace
    , handleLogWriter
    , renderLogMessages
    -- * Tracing
    , LogObserve(..)
    , ObservationHandle
    , surround
    , surroundDebug
    , surroundInfo
    , surroundWarn
    -- ** Handlers
    , handleObserveLog
    , handleObserve
    ) where

import           Control.Lens                            (Prism', makeLenses, prism', review)
import           Control.Monad.Freer
import           Control.Monad.Freer.Extras              (raiseUnder)
import           Control.Monad.Freer.State               (State, get, put, runState)
import           Control.Monad.Freer.Writer              (Writer (..), tell)
import           Data.Aeson                              (FromJSON, ToJSON)
import           Data.Foldable                           (for_, traverse_)
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

-- | An abstract type used to tie the beginning and end of observations
--   together.
newtype ObservationHandle = ObservationHandle Integer

data LogObserve a r where
    LObserveBefore :: a -> LogObserve a ObservationHandle
    LObserveAfter  :: ObservationHandle -> LogObserve a ()

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

logError :: forall a effs. Member (LogMsg a) effs => a -> Eff effs ()
logError m = send $ LMessage (LogMessage Error m)

-- | Re-interpret a logging effect by mapping the
--   log messages.
--   (Does the same thing as 'Covariant.contramap' for
--   'Control.Tracer.Trace')
mapLog ::
    forall a b c effs.
    Member (LogMsg b) effs
    => (a -> b)
    -> Eff (LogMsg a ': effs) c
    -> Eff effs c
mapLog f = interpret $ \case
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
    mapLog (Render.renderStrict . layoutPretty defaultLayoutOptions . pretty)

-- | Re-interpret a 'Writer' effect by writing the events to the log
handleWriterLog ::
    forall a f effs.
    ( Member (LogMsg a) effs
    , Traversable f
    )
    => (a -> LogLevel)
    -> Eff (Writer (f a) ': effs)
    ~> Eff effs
handleWriterLog f = interpret $ \case
    Tell es -> traverse_ (\a -> send $ LMessage $ LogMessage (f a) a) es

-- | Re-interpret a 'Log' effect with a 'Writer'
handleLogWriter ::
    forall a w effs.
    ( Member (Writer w) effs
    )
    => Prism' w (LogMessage a)
    -> LogMsg a
    ~> Eff effs
handleLogWriter p = \case
    LMessage msg -> tell @w (review p msg)

-- | Ignore all log messages.
handleLogIgnore :: Eff (LogMsg a ': effs) ~> Eff effs
handleLogIgnore = interpret $ \case
    LMessage _ -> pure ()

-- | Write the log to stdout using 'Debug.Trace.trace'
handleLogTrace :: Eff (LogMsg String ': effs) ~> Eff effs
handleLogTrace = interpret $ \case
    LMessage msg -> Trace.trace (Render.renderString . layoutPretty defaultLayoutOptions . pretty $ msg) (pure ())

-- | Write a log message before and after an action.
surround :: forall v a effs. Member (LogObserve v) effs => v -> Eff effs a -> Eff effs a
surround v action = do
    i <- send $ LObserveBefore v
    result <- action
    send @(LogObserve v) $ LObserveAfter i
    pure result

-- | @surroundInfo = surround Info@
surroundInfo :: Member (LogObserve (LogMessage v)) effs => v -> Eff effs a -> Eff effs a
surroundInfo = surround . LogMessage Info

-- | @surroundDebug = surround Debug@
surroundDebug :: Member (LogObserve (LogMessage v)) effs => v -> Eff effs a -> Eff effs a
surroundDebug = surround . LogMessage Debug

-- | @surroundWarn = surround Warn@
surroundWarn :: Member (LogObserve (LogMessage v)) effs => v -> Eff effs a -> Eff effs a
surroundWarn = surround . LogMessage Warning

-- | How did the observed action end
data ExitMode =
    Regular -- ^ The action was run to completion
    | Irregular -- ^ Execution of the observed action was cut short. This can happen if you use 'LogObserve' in combination with 'Error', 'NonDet', 'Prompt' or similar effects.
    deriving (Eq, Ord, Show)

-- | An observation with measurements before and after running an action.
data Observation v s =
    Observation
        { obsLabel :: v -- ^ Description of the action
        , obsStart :: s -- ^ Measurement before running the action
        , obsEnd   :: s -- ^ Measurement after running the action
        , obsExit  :: ExitMode -- ^ 'ExitMode' of the action.
        }

--  | An 'Observation' that doesn't have an 'obsEnd' value yet.
data PartialObservation v s =
    PartialObservation
        { obsMsg   :: v
        , obsValue :: s
        , obsDepth :: Integer
        }

-- | State of partial observations
data ObsState v s =
    ObsState
        { obsMaxDepth :: Integer
        , obsPartials :: [PartialObservation v s]
        }

initialState :: ObsState v s
initialState = ObsState 0 []

-- see note [Logging and Tracing]
-- | Handle the 'LogObserve' effect by recording observations
--   @s@ before and after the observed action, and turning
--   them into 'LogMessage (Observation s)' values.
handleObserve ::
    forall v s effs.
    Eff effs s -- ^ How to get the current 's'
    -> (Observation v s -> Eff effs ()) -- what to do with the observation
    -> Eff (LogObserve v ': effs)
    ~> Eff effs
handleObserve getCurrent handleObs =
    handleFinalState
    . runState @(ObsState v s) initialState
    . hdl
    . raiseUnder @effs @(LogObserve v) @(State (ObsState v s))
    where
        -- empty the stack of partial observations at the very end.
        handleFinalState :: forall a. Eff effs (a, (ObsState v s)) -> Eff effs a
        handleFinalState action = do
            (result, finalState) <- action
            _ <- handleObserveAfter finalState 0
            pure result

        -- when an action with the given depth is finished, take the final
        -- measurement and clear the stack of partial observations.
        handleObserveAfter :: ObsState v s -> Integer -> Eff effs (ObsState v s)
        handleObserveAfter ObsState{obsPartials} i = do
                current <- getCurrent
                let (finishedPartials, remainingPartials) = span ((<=) i . obsDepth) obsPartials
                for_ finishedPartials $ \PartialObservation{obsMsg, obsValue,obsDepth} -> do
                    -- we assume that a 'PartialObservation' was completed
                    -- regularly if it is handled at its own depth level.
                    -- If the @obsDepth@ is greater than @i@ then one or more
                    -- 'LObserveAfter' calls were skipped, which we note with
                    -- 'Irregular'.
                    let exitMode = if obsDepth == i then Regular else Irregular
                        message  = Observation{obsLabel=obsMsg, obsStart=obsValue, obsEnd=current, obsExit=exitMode}
                    handleObs message
                pure ObsState{obsMaxDepth=i - 1, obsPartials=remainingPartials}

        -- hdl :: Eff (LogObserve v ': State (ObsState v s) ': effs)
        --     ~> Eff (State (ObsState v s) ': effs)
        hdl = interpret $ \case
            LObserveBefore vl -> do
                current <- raise getCurrent
                ObsState{obsMaxDepth, obsPartials} <- get
                let newMaxDepth = obsMaxDepth + 1
                    msg = PartialObservation
                            { obsMsg = vl
                            , obsValue = current
                            , obsDepth = newMaxDepth
                            }
                put ObsState{obsMaxDepth=newMaxDepth,obsPartials=msg:obsPartials}
                pure (ObservationHandle newMaxDepth)
            LObserveAfter (ObservationHandle i) -> do
                currentState <- get @(ObsState v s)
                newState <- raise (handleObserveAfter currentState i)
                put newState

-- | Interpret the 'LogObserve' effect by logging a "start" message
--   before the action and an "end" message after the action.
handleObserveLog ::
    forall effs.
    Member (LogMsg Text) effs
    => Eff (LogObserve (LogMessage Text) ': effs)
    ~> Eff effs
handleObserveLog =
    handleObserve (pure ()) handleAfter
    . interpose handleBefore
        where
            handleBefore :: LogObserve (LogMessage Text) ~> Eff (LogObserve (LogMessage Text) ': effs)
            handleBefore = \case
                    LObserveBefore msg -> do
                        let msg' = fmap  (<> " start") msg
                        send $ LMessage msg'
                        send $ LObserveBefore msg
                    LObserveAfter i -> send @(LogObserve (LogMessage Text)) $ LObserveAfter i
            handleAfter Observation{obsLabel, obsExit} = do
                let msg' = fmap (\lbl -> case obsExit of { Regular -> lbl <> " end"; Irregular -> lbl <> " end (irregular)"} ) obsLabel
                send $ LMessage msg'
