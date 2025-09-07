module Benchmarks.Misc (makeBenchmarks) where

import Common
import Generators
import PlutusBenchmark.Common (EvaluationContext)

import PlutusCore

import Criterion.Main
import System.Random (StdGen)


-- mkPairData takes two 'Data' arguments d1 and d2 and creates the pair
-- (d1,d2).  This shouldn't depend on the size of the argumnts, but we'll run it
-- with a selection of different sizes just to make sure.
benchMkPairData :: EvaluationContext -> Benchmark
benchMkPairData evalCtx =
    createTwoTermBuiltinBench evalCtx MkPairData [] l1 l2
        where l1 = take 20 dataSample
              l2 = take 20 (drop 20 dataSample)

benchUnitArgBuiltin :: EvaluationContext -> DefaultFun -> Benchmark
benchUnitArgBuiltin evalCtx fun = createOneTermBuiltinBench evalCtx fun [] (take 100 $ repeat ())

makeBenchmarks :: EvaluationContext -> StdGen -> [Benchmark]
makeBenchmarks evalCtx _gen =
  [ benchMkPairData evalCtx]
  <> (benchUnitArgBuiltin evalCtx <$> [MkNilData, MkNilPairData])
