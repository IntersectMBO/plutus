module Main (main) where

import Criterion.Main
import GHC.IO (evaluate)
import PlutusBenchmark.Common (getConfig, mkMostRecentEvalCtx)
import PlutusLedgerApi.Common (EvaluationContext)

main :: IO ()
main = do
  config <- getConfig 15.0
  evalCtx <- evaluate mkMostRecentEvalCtx
  defaultMainWith config (benchmarks evalCtx)

benchmarks :: EvaluationContext -> [Benchmark]
benchmarks _evalCtx = []
