module Benchmarks.Data (makeBenchmarks) where

import           Benchmarks.Common

import           PlutusCore

import           Criterion.Main
import           System.Random     (StdGen)

benchChooseData :: StdGen -> Benchmark
benchChooseData gen = bgroup "UNIMPLEMENTED: ChooseData" []

benchConstrData :: StdGen -> Benchmark
benchConstrData gen = bgroup "UNIMPLEMENTED: ConstrData" []

benchMapData :: StdGen -> Benchmark
benchMapData gen = bgroup "UNIMPLEMENTED: MapData" []

benchListData :: StdGen -> Benchmark
benchListData gen = bgroup "UNIMPLEMENTED: ListData" []

benchIData :: StdGen -> Benchmark
benchIData gen = bgroup "UNIMPLEMENTED: IData" []

benchBData :: StdGen -> Benchmark
benchBData gen = bgroup "UNIMPLEMENTED: BData" []

benchUnConstrData :: StdGen -> Benchmark
benchUnConstrData gen = bgroup "UNIMPLEMENTED: UnConstrData" []

benchUnMapData :: StdGen -> Benchmark
benchUnMapData gen = bgroup "UNIMPLEMENTED: UnMapData" []

benchUnListData :: StdGen -> Benchmark
benchUnListData gen = bgroup "UNIMPLEMENTED: UnListData" []

benchUnIData :: StdGen -> Benchmark
benchUnIData gen = bgroup "UNIMPLEMENTED: UnIData" []

benchUnBData :: StdGen -> Benchmark
benchUnBData gen = bgroup "UNIMPLEMENTED: UnBData" []

benchEqualsData :: StdGen -> Benchmark
benchEqualsData gen = bgroup "UNIMPLEMENTED: EqualsData" []


makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen = [ benchChooseData gen,
                       benchConstrData gen,
                       benchMapData gen,
                       benchListData gen,
                       benchIData gen,
                       benchBData gen,
                       benchUnConstrData gen,
                       benchUnMapData gen,
                       benchUnListData gen,
                       benchUnIData gen,
                       benchUnBData gen,
                       benchEqualsData gen
                     ]
