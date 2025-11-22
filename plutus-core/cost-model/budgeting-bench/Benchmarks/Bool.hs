module Benchmarks.Bool (makeBenchmarks) where

import Common
import Generators

import PlutusCore

import Criterion.Main
import System.Random (StdGen)

-- We only have ifThenElse at the moment, which should be constant cost.
-- We check that with a bunch of bytestrings of different sizes.

benchIfThenElse :: Benchmark
benchIfThenElse =
  let name = IfThenElse
      resultSizes = [100, 500, 1000, 2000, 5000, 10000, 20000]
      results1 = makeSizedByteStrings seedA resultSizes
      results2 = makeSizedByteStrings seedB resultSizes
      mkBMs ty b =
        [ bgroup
            (showMemoryUsage r1)
            [ benchDefault (showMemoryUsage r2) $ mkApp3 name ty b r1 r2
            | r2 <- results2
            ]
        | r1 <- results1
        ]
   in bgroup (show name) (mkBMs [bytestring] True ++ mkBMs [bytestring] False)

-- This gives 98 datapoints (2*7*7).

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks _gen = [benchIfThenElse]
