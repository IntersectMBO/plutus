{-# LANGUAGE TypeOperators #-}

module Benchmarks.Unit (makeBenchmarks) where

import PlutusCore
import PlutusCore.Evaluation.Machine.ExMemoryUsage

import Common
import Generators

import Control.DeepSeq (NFData)
import Criterion.Main
import System.Random (StdGen)

createChooseUnitBench
  :: (DefaultUni `HasTermLevel` a, ExMemoryUsage a, NFData a)
  => Type TyName DefaultUni ()
  -> [a]
  -> Benchmark
createChooseUnitBench ty xs =
  bgroup (show name) [bgroup (showMemoryUsage ()) [mkBM x | x <- xs]]
  where
    name = ChooseUnit
    mkBM x = benchDefault (showMemoryUsage x) $ mkApp2 name [ty] () x

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen =
  [ createChooseUnitBench integer numbers
  , createChooseUnitBench bytestring bytestrings
  ]
  where
    (numbers, _) = makeSizedIntegers gen (fmap (100 *) [1 .. 50])
    bytestrings = fmap (makeSizedByteString seedA) (fmap (100 *) [51 .. 100])

-- The time should be independent of the type and size of the input,
-- but let's vary them to make sure.
