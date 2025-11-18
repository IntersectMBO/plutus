module Benchmarks.Pairs (makeBenchmarks) where

import Common
import Generators

import PlutusCore

import Criterion.Main
import System.Random (StdGen)

-- The pair projection operations should be constant time, but we check that by
-- giving it a list of pairs whose components are of increasing size.
benchPairOp :: StdGen -> DefaultFun -> Benchmark
benchPairOp gen fun =
  createOneTermBuiltinBench fun [integer, bytestring] pairs
  where
    pairs = zip ints bytestrings
    (ints, _) = makeSizedIntegers gen [1 .. 100]
    bytestrings = makeSizedByteStrings seedA [1 .. 100]

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen = benchPairOp gen <$> [FstPair, SndPair]
