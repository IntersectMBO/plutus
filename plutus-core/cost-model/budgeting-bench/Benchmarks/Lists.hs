module Benchmarks.Lists (makeBenchmarks) where

import           Benchmarks.Common

import           Criterion.Main
import           System.Random     (StdGen)

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks _gen = []

{- TODO:
   chooseList
   mkCons
   headList
   tailList
   nullList
-}

