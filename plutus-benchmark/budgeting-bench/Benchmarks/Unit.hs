{-# LANGUAGE TypeOperators #-}

module Benchmarks.Unit (makeBenchmarks) where

import Common
import Generators
import PlutusBenchmark.Common (EvaluationContext)

import PlutusCore
import PlutusCore.Evaluation.Machine.ExMemoryUsage

import Control.DeepSeq (NFData)
import Criterion.Main
import System.Random (StdGen)

createChooseUnitBench
    :: (DefaultUni `HasTermLevel` a, ExMemoryUsage a, NFData a)
    => EvaluationContext
    -> Type TyName DefaultUni ()
    -> [a]
    -> Benchmark
createChooseUnitBench evalCtx ty xs =
    bgroup (show name) [bgroup (showMemoryUsage ()) [mkBM x | x <- xs]]
        where name = ChooseUnit
              mkBM x = benchWithCtx evalCtx (showMemoryUsage x) $ mkApp2 name [ty] () x

makeBenchmarks :: EvaluationContext -> StdGen -> [Benchmark]
makeBenchmarks evalCtx gen =
  [ createChooseUnitBench evalCtx integer numbers
  , createChooseUnitBench evalCtx bytestring bytestrings
  ] where (numbers, _) = makeSizedIntegers gen (fmap (100 *) [1..50])
          bytestrings = fmap (makeSizedByteString seedA) (fmap (100 *) [51..100])
          -- The time should be independent of the type and size of the input,
          -- but let's vary them to make sure.
