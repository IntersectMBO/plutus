module Benchmarks.Pairs (makeBenchmarks) where

import           Benchmarks.Common

import           PlutusCore

import           Criterion.Main
import           System.Random     (StdGen)

benchPairOp :: StdGen -> DefaultFun -> Benchmark
benchPairOp gen fun = bgroup ("UNIMPLEMENTED: " ++ show fun) []

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen = benchPairOp gen <$> [FstPair, SndPair]
