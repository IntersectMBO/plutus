--------------------------------------------------------------------------------
-- This module is copied from https://github.com/IntersectMBO/plutus/pull/7344
-- Do not merge! merge #7344 instead.
--------------------------------------------------------------------------------

{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE NumericUnderscores  #-}
{-# LANGUAGE TupleSections       #-}

module Benchmarks.Values (makeBenchmarks) where

import Prelude

import Common
import Control.Monad (replicateM)
import Criterion.Main (Benchmark)
import Data.ByteString (ByteString)
import Data.Int (Int64)
import PlutusCore (DefaultFun (NegateValue, ScaleValue))
import PlutusCore.Builtin (BuiltinResult (..))
import PlutusCore.Value (K, Value)
import PlutusCore.Value qualified as Value
import System.Random.Stateful (StatefulGen, StdGen, runStateGen_, uniformByteStringM, uniformRM)

----------------------------------------------------------------------------------------------------
-- Benchmarks --------------------------------------------------------------------------------------

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen =
  [ negateValueBenchMark gen
  , scaleValueBenchMark gen
  ]

negateValueBenchMark :: StdGen -> Benchmark
negateValueBenchMark gen =
  createOneTermBuiltinBench NegateValue [] (generateTestValues gen)

scaleValueBenchMark :: StdGen -> Benchmark
scaleValueBenchMark gen =
  createTwoTermBuiltinBenchElementwise ScaleValue [] ((-1 :: Integer, ) <$> generateTestValues gen)

----------------------------------------------------------------------------------------------------
-- Value Generators --------------------------------------------------------------------------------

-- | Generate common test values for benchmarking
generateTestValues :: StdGen -> [Value]
generateTestValues gen = runStateGen_ gen \g ->
  -- Empty value as edge case
  (Value.empty :)
    <$>
    -- Random tests for parameter spread (100 combinations)
    replicateM 100 (generateValue g)

-- | Generate Value with random budget between 1 and 30,000 bytes
generateValue :: (StatefulGen g m) => g -> m Value
generateValue g = do
  maxEntries <- uniformRM (1, maxValueEntries maxValueInBytes) g
  generateValueMaxEntries maxEntries g
 where
  -- Maximum budget for Value generation (30,000 bytes)
  maxValueInBytes :: Int
  maxValueInBytes = 30_000

  -- Calculate maximum possible number of entries with maximal key sizes that fits in the budget
  maxValueEntries :: Int -> Int
  maxValueEntries budget =
    let bytesPerEntry =
          {- bytes per policy -} Value.maxKeyLen
            {- bytes per token -} + Value.maxKeyLen
            {- bytes per quantity (Int64 takes up 8 bytes) -} + 8
     in budget `div` bytesPerEntry

-- | Generate Value within total size budget
generateValueMaxEntries :: (StatefulGen g m) => Int -> g -> m Value
generateValueMaxEntries maxEntries g = do
  -- Uniform random distribution: cover full range from many policies (few tokens each)
  -- to few policies (many tokens each)
  numPolicies <- uniformRM (1, maxEntries) g
  let tokensPerPolicy = if numPolicies > 0 then maxEntries `div` numPolicies else 0

  generateConstrainedValue numPolicies tokensPerPolicy g

-- | Generate constrained Value
generateConstrainedValue
  :: (StatefulGen g m)
  => Int -- Number of policies
  -> Int -- Number of tokens per policy
  -> g
  -> m Value
generateConstrainedValue numPolicies tokensPerPolicy g = do
  policyIds <- replicateM numPolicies (generateKey g)
  tokenNames <- replicateM tokensPerPolicy (generateKey g)
  quantity <- uniformRM (-(2^127), 2^(127 :: Integer) - 1) g

  case Value.quantity quantity of
    Just q -> do
      let
        nestedMap :: [(K, [(K, Value.Quantity)])]
        nestedMap = (,(,q) <$> tokenNames) <$> policyIds

      case Value.fromList nestedMap of
        BuiltinSuccess v' -> pure v'
        _                 -> error "impossible"
    Nothing -> error "impossible"

----------------------------------------------------------------------------------------------------
-- Other Generators --------------------------------------------------------------------------------

-- | Generate random key (always maxKeyLen bytes for Cardano compliance)
generateKey :: (StatefulGen g m) => g -> m K
generateKey g = do
  bs <- uniformByteStringM Value.maxKeyLen g
  case Value.k bs of
    Just key -> pure key
    Nothing  -> error "Internal error: maxKeyLen key should always be valid"

-- | Generate random key as ByteString (for lookup arguments)
generateKeyBS :: (StatefulGen g m) => g -> m ByteString
generateKeyBS = uniformByteStringM Value.maxKeyLen
