module PlutusTx.Plugin.Timing (timeStage) where

import Control.Exception (evaluate)
import Control.Monad.IO.Class (MonadIO, liftIO)
import GHC.Clock (getMonotonicTimeNSec)
import System.CPUTime (getCPUTime)
import System.IO (hPutStrLn, stderr)

timeStage
  :: MonadIO monad => Bool -> String -> String -> (result -> ()) -> monad result -> monad result
timeStage False _ _ _ action = action
timeStage True scope stage forceResult action = do
  wallStart <- liftIO getMonotonicTimeNSec
  cpuStart <- liftIO getCPUTime
  result <- action
  liftIO $ evaluate (forceResult result)
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
