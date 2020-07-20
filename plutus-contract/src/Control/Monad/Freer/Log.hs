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
    , LogMsg(..)
    , LogObserve(..)
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
    , contramapLog
    -- * Handlers
    , writeToLog
    , ignoreLog
    , traceLog
    , logToWriter
    , observeAsLogMessage
    , renderLogMessages
    , handleObserve
    , runLog
    ) where

import Control.Lens (Prism', review, makeLenses, prism')
import           Control.Monad.Freer
import Control.Monad.Freer.Extras (raiseUnder)
import Control.Monad.Freer.Error (Error, runError)
import Control.Monad.Freer.State (State, get, put, runState)
import           Control.Monad.Freer.Writer              (Writer (..), tell)
import           Data.Aeson                              (FromJSON, ToJSON)
import           Data.Foldable                           (traverse_)
import           Data.Text                               (Text)
import           Data.Text.Prettyprint.Doc               hiding (surround)
import qualified Data.Text.Prettyprint.Doc.Render.String as Render
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc.Render.Text   as Render
import qualified Debug.Trace                             as Trace
import           GHC.Generics                            (Generic)

type Log = LogMsg Text

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

renderLogMessages ::
    forall a effs.
    ( Member (LogMsg Text) effs
    , Pretty a
    )
    => Eff (LogMsg a ': effs)
    ~> Eff effs
renderLogMessages = 
    contramapLog (Render.renderStrict . layoutPretty defaultLayoutOptions . pretty)

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

data ExitMode =
    Regular
    | Irregular -- execution of the observed action was cut short. This can happen if you use 'LogObserve' in combination with 'Error', 'NonDet', 'Prompt' or similar effects.
    deriving (Eq, Ord, Show)

data Observation s =
    Observation
        { obsLabel :: Text
        , obsStart :: s
        , obsEnd :: s
        , obsExit :: ExitMode
        }

data PartialObservation s =
    PartialObservation
        { obsMsg :: LogMessage Text
        , obsValue :: s
        , obsDepth :: Integer
        }

data ObsState s =
    ObsState
        { obsMaxDepth :: Integer
        , obsPartials :: [PartialObservation s]
        }

initialState :: ObsState s
initialState = ObsState 0 []

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
        handleFinalState action = do
            (result, finalState) <- action
            _ <- handleObserveAfter finalState 0
            pure result
        handleObserveAfter :: ObsState s -> Integer -> Eff effs (ObsState s)
        handleObserveAfter ObsState{obsPartials} i = do
                current <- getCurrent
                let (relevantPartials, remainingPartials) = span ((<=) i . obsDepth) obsPartials
                flip traverse_ relevantPartials $ \PartialObservation{obsMsg, obsValue,obsDepth} -> do
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
    
-- | Write the log to stdout using 'Debug.Trace.trace'
traceLog :: Eff (LogMsg String ': effs) ~> Eff effs
traceLog = interpret $ \case
    LMessage msg -> Trace.trace (Render.renderString . layoutPretty defaultLayoutOptions . pretty $ msg) (pure ())

runLog :: Eff [Error String, LogObserve,  LogMsg Text, LogMsg String, IO] a -> IO (Either String a)
runLog = 
    runM
    . traceLog
    . contramapLog Text.unpack
    . observeAsLogMessage
    . runError