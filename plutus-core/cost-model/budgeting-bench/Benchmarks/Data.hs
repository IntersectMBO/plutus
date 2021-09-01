{-# LANGUAGE LambdaCase #-}

module Benchmarks.Data (makeBenchmarks) where

import           Benchmarks.Common
import           Benchmarks.Generators

import           PlutusCore
import           PlutusCore.Data

import           Criterion.Main
import qualified Hedgehog                as H
import qualified Hedgehog.Internal.Gen   as G
import qualified Hedgehog.Internal.Range as R
import           System.Random           (StdGen)

benchChooseData :: StdGen -> Benchmark
benchChooseData gen = bgroup "UNIMPLEMENTED: ChooseData" []
-- Choose one of five alternatives depending on which constructor you've got.

benchConstrData :: StdGen -> Benchmark
benchConstrData gen = bgroup "UNIMPLEMENTED: ConstrData" []
-- Apply Constr to an integer and a list of Data

benchMapData :: StdGen -> Benchmark
benchMapData gen = undefined
--    createOneTermBuiltinBench MapData [] (genSample seedA (G.list (R.singleton 50) genDataPair))
--
benchListData :: StdGen -> Benchmark
benchListData gen = bgroup "UNIMPLEMENTED: ListData" []
-- Apply List

-- Apply I
benchIData :: StdGen -> Benchmark
benchIData gen =
    createOneTermBuiltinBench IData [] ints
        where  (ints, _) = makeSizedIntegers gen [1..50]

-- Apply B
benchBData :: StdGen -> Benchmark
benchBData gen =
    createOneTermBuiltinBench BData [] bss
        where bss = makeSizedByteStrings seedA (fmap (100*) [1..50])

benchUnConstrData :: StdGen -> Benchmark
benchUnConstrData gen = bgroup "UNIMPLEMENTED: UnConstrData" []
-- Match against Constr, failing otherwise

benchUnMapData :: StdGen -> Benchmark
benchUnMapData gen = bgroup "UNIMPLEMENTED: UnMapData" []
-- Match against Map, failing otherwise

benchUnListData :: StdGen -> Benchmark
benchUnListData gen = bgroup "UNIMPLEMENTED: UnListData" []
-- Match against List, failing otherwise

benchUnIData :: StdGen -> Benchmark
benchUnIData gen = bgroup "UNIMPLEMENTED: UnIData" []
-- Match against I, failing otherwise

benchUnBData :: StdGen -> Benchmark
benchUnBData gen = bgroup "UNIMPLEMENTED: UnBData" []
-- Match against B, failing otherwise

benchEqualsData :: Benchmark
benchEqualsData =
    createTwoTermBuiltinBenchElementwise EqualsData [] args1 args2
        where args1 = undefined :: [Data] -- genDataSample 200
              args2 = fmap copyData args1


makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen = [benchEqualsData, benchIData gen, benchBData gen]

    -- [ benchChooseData gen,
                     --   benchConstrData gen,
                     --   benchMapData gen,
                     --   benchListData gen,
                     --   benchIData gen,
                     --   benchBData gen,
                     --   benchUnConstrData gen,
                     --   benchUnMapData gen,
                     --   benchUnListData gen,
                     --   benchUnIData gen,
                     --   benchUnBData gen,
                     --   benchEqualsData gen
                     -- ]
