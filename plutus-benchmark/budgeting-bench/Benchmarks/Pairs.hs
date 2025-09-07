module Benchmarks.Pairs (makeBenchmarks) where

import Common
import Generators
import PlutusBenchmark.Common (EvaluationContext)

import Criterion.Main
import PlutusCore
import System.Random (StdGen)


-- The pair projection operations should be constant time, but we check that by
-- giving it a list of pairs whose components are of increasing size.
benchPairOp :: EvaluationContext -> StdGen -> DefaultFun -> Benchmark
benchPairOp evalCtx gen fun =
    createOneTermBuiltinBench evalCtx fun [integer, bytestring] pairs
        where pairs = zip ints bytestrings
              (ints, _)   = makeSizedIntegers gen [1..100]
              bytestrings = makeSizedByteStrings seedA [1..100]

makeBenchmarks :: EvaluationContext -> StdGen -> [Benchmark]
makeBenchmarks evalCtx gen = benchPairOp evalCtx gen <$> [FstPair, SndPair]
