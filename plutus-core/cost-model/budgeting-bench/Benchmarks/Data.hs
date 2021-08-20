module Benchmarks.Data (makeBenchmarks) where

import           Benchmarks.Common

import           PlutusCore

import           Criterion.Main
import           System.Random     (StdGen)

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks _gen = []



{- TODO:
   chooseData
   constrData
   mapData
   listData
   iData
   bData
   unConstrData
   unMapData
   unListData
   unIData
   unBData
   equalsData

-}




