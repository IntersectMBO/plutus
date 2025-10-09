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
import PlutusCore (DefaultFun (LookupCoin, UnValueData, ValueContains, ValueData))
import PlutusCore.Evaluation.Machine.ExMemoryUsage (LogValueOuterOrMaxInner (..),
                                                    ValueTotalSize (..))
import PlutusCore.Value (K, Value)
import PlutusCore.Value qualified as Value
import System.Random.Stateful (StatefulGen, StdGen, runStateGen_, uniformByteStringM, uniformRM)

----------------------------------------------------------------------------------------------------
-- Benchmarks --------------------------------------------------------------------------------------

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen =
  [ lookupCoinBenchmark gen
  , valueContainsBenchmark gen
  , valueDataBenchmark gen
  , unValueDataBenchmark gen
  ]

----------------------------------------------------------------------------------------------------
-- LookupCoin --------------------------------------------------------------------------------------

lookupCoinBenchmark :: StdGen -> Benchmark
lookupCoinBenchmark gen =
  createThreeTermBuiltinBenchElementwiseWithWrappers
    (id, id, LogValueOuterOrMaxInner) -- Wrap Value argument to report outer/max inner size with log
    LookupCoin -- the builtin fun
    [] -- no type arguments needed (monomorphic builtin)
    (lookupCoinArgs gen) -- the argument combos to generate benchmarks for

lookupCoinArgs :: StdGen -> [(ByteString, ByteString, Value)]
lookupCoinArgs gen = runStateGen_ gen \(g :: g) -> do
  -- Add search keys to common test values
  let testValues = generateTestValues gen
  commonWithKeys <- mapM (withSearchKeys g . pure) testValues

  -- Additional tests specific to lookupCoin
  let valueSizes = [(100, 10), (500, 20), (1_000, 50), (2_000, 100)]
  additionalTests <-
    sequence $
      -- Value size tests (number of policies × tokens per policy)
      [ withSearchKeys g (generateConstrainedValue numPolicies tokensPerPolicy g)
      | (numPolicies, tokensPerPolicy) <- valueSizes
      ]
        -- Additional random tests for parameter spread
        <> replicate 100 (withSearchKeys g (generateValue g))
  pure $ commonWithKeys ++ additionalTests

-- | Add random search keys to a Value (keys may or may not exist in the Value)
withSearchKeys :: (StatefulGen g m) => g -> m Value -> m (ByteString, ByteString, Value)
withSearchKeys g genValue = do
  value <- genValue
  key1 <- generateKeyBS g
  key2 <- generateKeyBS g
  pure (key1, key2, value)

----------------------------------------------------------------------------------------------------
-- ValueContains -----------------------------------------------------------------------------------

valueContainsBenchmark :: StdGen -> Benchmark
valueContainsBenchmark gen =
  createTwoTermBuiltinBenchElementwiseWithWrappers
    (LogValueOuterOrMaxInner, ValueTotalSize)
    -- Container: outer/maxInner with log, Contained: totalSize
    ValueContains -- the builtin fun
    [] -- no type arguments needed (monomorphic builtin)
    (valueContainsArgs gen) -- the argument combos to generate benchmarks for

valueContainsArgs :: StdGen -> [(Value, Value)]
valueContainsArgs gen = runStateGen_ gen \g -> replicateM 100 do
  -- Generate a random container value
  container <- generateValue g
  -- Select a random subset of entries from the container to ensure contained ⊆ container
  containedSize <- uniformRM (0, Value.totalSize container) g
  -- Take the first containedSize entries to ensure contained ⊆ container
  let selectedEntries = take containedSize (Value.toFlatList container)

  -- Group selected entries back by policy
  let contained =
        Value.fromList
          [ (policyId, [(tokenName, quantity)])
          | (policyId, tokenName, quantity) <- selectedEntries
          ]

  pure (container, contained)

----------------------------------------------------------------------------------------------------
-- ValueData ---------------------------------------------------------------------------------------

valueDataBenchmark :: StdGen -> Benchmark
valueDataBenchmark gen = createOneTermBuiltinBench ValueData [] (generateTestValues gen)

----------------------------------------------------------------------------------------------------
-- UnValueData -------------------------------------------------------------------------------------

unValueDataBenchmark :: StdGen -> Benchmark
unValueDataBenchmark gen =
  createOneTermBuiltinBench UnValueData [] (Value.valueData <$> generateTestValues gen)

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

  let quantity :: Integer
      quantity = fromIntegral (maxBound :: Int64)

      nestedMap :: [(K, [(K, Integer)])]
      nestedMap = (,(,quantity) <$> tokenNames) <$> policyIds

  pure $ Value.fromList nestedMap

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
