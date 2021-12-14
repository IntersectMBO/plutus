{-# language CPP #-}
module Main (main) where

import Criterion.Main
import System.Clock

#if MIN_VERSION_base(4,11,0)
import GHC.Clock
#endif

main :: IO ()
main = defaultMain [
    bgroup "getTime" [
        bench "Monotonic" $ whnfIO (getTime Monotonic)
      , bench "Realtime" $ whnfIO (getTime Realtime)
      , bench "ProcessCPUTime" $ whnfIO (getTime ProcessCPUTime)
      , bench "ThreadCPUTime" $ whnfIO (getTime ThreadCPUTime)
      , bench "MonotonicRaw" $ whnfIO (getTime MonotonicRaw)
      , bench "Boottime" $ whnfIO (getTime Boottime)
      , bench "MonotonicCoarse" $ whnfIO (getTime MonotonicCoarse)
      , bench "RealtimeCoarse" $ whnfIO (getTime RealtimeCoarse)
      ]
#if MIN_VERSION_base(4,11,0)
  , bench "GHC.Clock.getMonotonicTimeNSec" $ whnfIO getMonotonicTimeNSec
#endif
  ]
