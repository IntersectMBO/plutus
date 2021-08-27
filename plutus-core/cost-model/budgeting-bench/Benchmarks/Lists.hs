module Benchmarks.Lists (makeBenchmarks) where

import           Benchmarks.Common

import           Criterion.Main
import           System.Random     (StdGen)

benchNullList :: Benchmark
benchNullList = undefined


makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks _gen = [benchNullList]

{- TODO:
   chooseList
   mkCons
   headList
   tailList
   nullList
-}

