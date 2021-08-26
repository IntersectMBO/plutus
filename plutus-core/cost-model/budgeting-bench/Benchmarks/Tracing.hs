module Benchmarks.Tracing (makeBenchmarks) where

import           PlutusCore

import           Benchmarks.Common

import           Criterion.Main
import           System.Random     (StdGen)

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks _gen = []

-- TODO: trace

