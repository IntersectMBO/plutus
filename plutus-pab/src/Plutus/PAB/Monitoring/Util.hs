{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Plutus.PAB.Monitoring.Util (
      handleLogMsgTrace
    , handleLogMsgTraceMap
    , handleObserveTrace
    , runLogEffects
    , convertLog
    , toSeverity
    ) where

import qualified Cardano.BM.Configuration.Model as CM
import           Cardano.BM.Data.Counter
import           Cardano.BM.Data.LogItem
import           Cardano.BM.Data.Severity
import           Cardano.BM.Data.SubTrace
import           Cardano.BM.Data.Trace
import           Cardano.BM.Observer.Monadic
import           Cardano.BM.Trace
import           Control.Monad                  (void)
import           Control.Monad.Catch            (MonadCatch)
import           Control.Monad.Freer
import           Control.Monad.Freer.Extras.Log (LogMsg (..), LogObserve (..), Observation (..))
import qualified Control.Monad.Freer.Extras.Log as L
import           Control.Monad.IO.Class         (MonadIO (..))
import           Data.Bifunctor                 (Bifunctor (..))
import           Data.Foldable                  (for_)
import           Data.Functor.Contravariant     (Contravariant (..))
import           Data.Maybe                     (fromMaybe)
import           Data.Text                      (Text)

toSeverity :: L.LogLevel -> Severity
toSeverity = \case
  L.Debug     -> Debug
  L.Info      -> Info
  L.Notice    -> Notice
  L.Warning   -> Warning
  L.Error     -> Error
  L.Critical  -> Critical
  L.Alert     -> Alert
  L.Emergency -> Emergency


-- | Handle the 'LogMsg' effect by logging messages to a 'Trace'
handleLogMsgTrace :: forall a m effs.
  ( LastMember m effs
  , MonadIO m
  )
  => Trace m a
  -> Eff (LogMsg a ': effs)
  ~> Eff effs
handleLogMsgTrace trace = interpret $ \case
  LMessage L.LogMessage{L._logLevel, L._logMessageContent} ->
    let defaultPrivacy = Public -- TODO: Configurable / add to 'L.LogMessage'?
    in sendM $ traceNamedItem trace defaultPrivacy (toSeverity _logLevel) _logMessageContent

-- | Handle the 'LogMsg' effect by logging messages to a mapped 'Trace'
handleLogMsgTraceMap :: forall b a m effs.
  ( LastMember m effs
  , MonadIO m
  )
  => (b -> a)
  -> Trace m a
  -> Eff (LogMsg b ': effs)
  ~> Eff effs
handleLogMsgTraceMap f t = handleLogMsgTrace (contramap (second (fmap f)) t)

runLogEffects ::
    forall m l.
    MonadIO m
    => Trace m l
    -> Eff '[LogMsg l, m]
    ~> m
runLogEffects trace = runM . handleLogMsgTrace trace


-- | Convert tracer structured log data
convertLog :: (a -> b) -> Trace m b -> Trace m a
convertLog f = contramap (second (fmap f))


-- | Handle the 'LogObserve' effect using the 'Cardano.BM.Observer.Monadic'
--   observer functions
handleObserveTrace ::
  forall effs m a.
  ( LastMember m effs
  , MonadIO m
  , MonadCatch m
  )
  => CM.Configuration
  -> Trace m a
  -> Eff (LogObserve (L.LogMessage Text) ': effs)
  ~> Eff effs
handleObserveTrace config t =

  -- We need to call 'observeOpen' and 'observeClose' with the appropriate
  -- arguments.
  --
  -- 'observeBefore' makes the call to 'observeOpen' and 'observeAfter'
  -- makes the call to 'observeClose.'

  let observeBefore :: L.LogMessage Text -> Eff effs (Maybe (SubTrace, CounterState))
      observeBefore L.LogMessage{L._logLevel, L._logMessageContent} = do

        -- find the correct subtrace using the logging config and the content
        -- of the message.
        subtrace <- fromMaybe Neutral <$> sendM @_ @effs (liftIO $ CM.findSubTrace config _logMessageContent)

        -- 'observeOpen' produces the state of the counters at the beginning of
        -- the action. We return 'counterState' and 'subtrace' so that
        -- they are available in 'observeAfter'.
        mCountersid <- sendM $ observeOpen subtrace (toSeverity _logLevel) t
        case mCountersid of
          Left _             -> pure Nothing
          Right counterState -> pure (Just (subtrace, counterState))

      observeAfter :: Observation (L.LogMessage Text) (Maybe (SubTrace, CounterState)) -> Eff effs ()
      observeAfter Observation{obsStart} =
        for_ obsStart $ \(subtrace, counterState) ->
          void $ sendM $ observeClose subtrace Info t counterState []

  in L.handleObserve
      observeBefore
      observeAfter
