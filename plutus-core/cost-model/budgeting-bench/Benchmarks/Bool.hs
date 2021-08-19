module Benchmarks.Bool (makeBenchmarks) where

import           Benchmarks.Common ()

import           Criterion.Main
import           System.Random     (StdGen)

-- We only have ifThenElse at the moment, and that's cheap (but we could benchmark to make sure)

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks _gen = []
