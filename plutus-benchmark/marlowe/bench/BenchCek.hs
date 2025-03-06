-- | Benchmarks for the CEK machine based on some Marlowe examples.
module Main where

import PlutusBenchmark.Common (benchProgramCek, mkMostRecentEvalCtx)
import Shared (runBenchmarks)

import Control.Exception (evaluate)

main :: IO ()
main = do
  evalCtx <- evaluate mkMostRecentEvalCtx
  runBenchmarks (benchProgramCek evalCtx)
