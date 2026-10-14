{-| Timing of Plinth compilation stages, enabled by the @dump-timings@ plugin option.

GHC's @GHC.Utils.Error.withTiming@ is not used because it reports only CPU time and
allocation, and only under GHC's own @-v@ or @-ddump-timings@ flags. 'timeStage' also
reports monotonic wall-clock time, tags each record with the module or expression it
belongs to, and is switched on by a plugin option without enabling GHC's timing dumps. -}
module PlutusTx.Plugin.Timing (timeStage) where

import Control.Exception (evaluate)
import Control.Monad.IO.Class (MonadIO, liftIO)
import GHC.Clock (getMonotonicTimeNSec)
import System.CPUTime (getCPUTime)
import System.IO (hPutStrLn, stderr)

{-| Run an action and print its wall-clock and CPU time to stderr as one
@PLINTH_TIMING@ line.

With forcing on, the result is evaluated with the given function before the clocks
stop. With timing off, the action runs as is: no clocks are read and the forcing
function is never called. If the action or the forcing throws, the exception
propagates and nothing is printed. The line is written after the clocks stop, so it
counts towards enclosing stages but not this one. -}
timeStage
  :: MonadIO monad
  => Bool
  -- ^ Whether to time the action at all.
  -> Bool
  -- ^ Whether to force the result before stopping the clocks.
  -> String
  -- ^ Module or expression scope.
  -> String
  -- ^ Stage name.
  -> (result -> ())
  -- ^ Forces the result; only called when timing and forcing are both on.
  -> monad result
  -- ^ Action to measure.
  -> monad result
timeStage False _ _ _ _ action = action
timeStage True forceResults scope stage forceResult action = do
  wallStart <- liftIO getMonotonicTimeNSec
  cpuStart <- liftIO getCPUTime
  result <- action
  if forceResults then liftIO $ evaluate (forceResult result) else pure ()
  cpuEnd <- liftIO getCPUTime
  wallEnd <- liftIO getMonotonicTimeNSec
  liftIO $
    hPutStrLn stderr $
      "PLINTH_TIMING\t"
        <> scope
        <> "\t"
        <> stage
        <> "\t"
        <> show (wallEnd - wallStart)
        <> "\t"
        <> show (cpuEnd - cpuStart)
  pure result
