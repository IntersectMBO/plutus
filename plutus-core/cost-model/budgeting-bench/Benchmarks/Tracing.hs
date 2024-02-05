module Benchmarks.Tracing (makeBenchmarks) where

import PlutusCore

import Common
import Generators

import Criterion.Main
import System.Random (StdGen)

-- We expect tracing (with a null emitter) to be constant time, but generate
-- multiple input sizes to be sure.
benchTracing :: StdGen -> Benchmark
benchTracing gen =
  createTwoTermBuiltinBench name [bytestring] inputs1 inputs2
  where
    name = Trace
    inputs1 = makeSizedTextStrings seedA [10, 20, 30, 40, 50, 100, 200, 300, 400, 500]
    -- The numbers above are the approximate number of characters in the trace message
    (inputs2, _) = makeSizedIntegers gen [1, 2, 3, 4, 5, 10, 20, 34, 40, 50]

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen = [benchTracing gen]
