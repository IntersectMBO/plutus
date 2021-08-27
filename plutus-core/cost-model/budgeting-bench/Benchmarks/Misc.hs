module Benchmarks.Misc (makeBenchmarks) where

import           Benchmarks.Common

import           PlutusCore

import           Criterion.Main
import           System.Random     (StdGen)



-- We need a selection of data of maybe ten different sizes
-- and then we need to benchmark mkPairData for all pairs
benchMkPairData :: StdGen -> Benchmark
benchMkPairData gen = bgroup "UNIMPLEMENTED: benchMkPairData" []

benchUnitArgBuiltin :: DefaultFun -> Benchmark
benchUnitArgBuiltin fun = createOneTermBuiltinBench fun [] (take 100 $ repeat ())

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen = [ benchMkPairData gen ]
                     <> (benchUnitArgBuiltin <$> [MkNilData, MkNilPairData])

