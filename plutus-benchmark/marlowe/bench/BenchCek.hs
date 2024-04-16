{- | Benchmarks for the CEK machine based on some Marlowe examples. -}

module Main where

import PlutusBenchmark.Common (benchProgramCek, mkEvalCtx)
import Shared (runBenchmarks)

import Control.DeepSeq (force)
import Control.Exception (evaluate)

main :: IO ()
main = do
  evalCtx <- evaluate $ force mkEvalCtx
  runBenchmarks (benchProgramCek evalCtx)
