{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module Benchmarks.Values (makeBenchmarks) where

import Prelude

import Common
import Control.Monad (replicateM)
import Criterion.Main (Benchmark)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Int (Int64)
import Data.List (sort)
import Data.Word (Word8)
import GHC.Stack (HasCallStack)
import PlutusCore (DefaultFun (LookupCoin, UnValueData, ValueContains, ValueData))
import PlutusCore.Builtin (BuiltinResult (BuiltinFailure, BuiltinSuccess, BuiltinSuccessWithLogs))
import PlutusCore.Evaluation.Machine.ExMemoryUsage
  ( ValueLogOuterSizeAddLogMaxInnerSize (..)
  , ValueTotalSize (..)
  )
import PlutusCore.Value (K, Value)
import PlutusCore.Value qualified as Value
import System.Random.Stateful (StatefulGen, StdGen, runStateGen_, uniformRM)

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
    (id, id, ValueLogOuterSizeAddLogMaxInnerSize) -- Wrap Value argument to report sum of log sizes
    LookupCoin -- the builtin fun
    [] -- no type arguments needed (monomorphic builtin)
    (lookupCoinArgs gen) -- the argument combos to generate benchmarks for

lookupCoinArgs :: StdGen -> [(ByteString, ByteString, Value)]
lookupCoinArgs gen = runStateGen_ gen \(g :: g) -> do
  {- Exhaustive power-of-2 combinations for BST worst-case benchmarking.

     Tests all combinations of sizes from powers and half-powers of 2.
     For each integer n ∈ {1..10}, includes both 2^n and 2^(n+0.5) ≈ 2^n * √2.

     This provides:
     - 400 total test points (20 × 20 grid)
     - Complete systematic coverage of depth range 2 to 21
     - Finer granularity between powers of 2
     - All distribution patterns (balanced, outer-heavy, inner-heavy)

     Size values: 2, 3, 4, 6, 8, 11, 16, 23, 32, 45, 64, 91, 128, 181,
                  256, 362, 512, 724, 1024, 1448

     Depth coverage:
     - Minimum depth: log₂(2) + log₂(2) ≈ 2
     - Maximum depth: log₂(1448) + log₂(1448) ≈ 21
  -}
  let
    -- Generate powers of 2 and their geometric means (half-powers)
    sizes =
      [ 2 ^ n -- 2^n
      | n <- [1 .. 10 :: Int]
      ]
        ++ [ round @Double (2 ^ n * sqrt 2) -- 2^(n+0.5)
           | n <- [1 .. 10 :: Int]
           ]

  sequence
    -- Generate worst-case lookups for each size combination
    [ withWorstCaseSearchKeys (generateConstrainedValueWithMaxPolicy numPolicies tokensPerPolicy g)
    | numPolicies <- sizes
    , tokensPerPolicy <- sizes
    ]

-- | Add worst-case search keys targeting the max-size inner map
withWorstCaseSearchKeys :: Monad m => m (Value, K, K) -> m (ByteString, ByteString, Value)
withWorstCaseSearchKeys genValueWithKeys = do
  (value, maxPolicyId, deepestToken) <- genValueWithKeys
  pure (Value.unK maxPolicyId, Value.unK deepestToken, value)

----------------------------------------------------------------------------------------------------
-- ValueContains -----------------------------------------------------------------------------------

valueContainsBenchmark :: StdGen -> Benchmark
valueContainsBenchmark gen =
  createTwoTermBuiltinBenchElementwiseWithWrappers
    (ValueTotalSize, ValueTotalSize)
    -- Both args use totalSize (total entry count)
    ValueContains -- the builtin fun
    [] -- no type arguments needed (monomorphic builtin)
    (valueContainsArgs gen) -- the argument combos to generate benchmarks for

valueContainsArgs :: StdGen -> [(Value, Value)]
valueContainsArgs gen = runStateGen_ gen \g -> do
  {- ValueContains uses nested Map.isSubmapOfBy with a splitLookup-based
     divide-and-conquer algorithm.

     Cost model uses totalSize for both arguments:
     - n₁ = total entry count of container
     - n₂ = total entry count of contained

     Early exit: If n₂ > n₁, returns False immediately (can't be a submap).
     This creates a straight line boundary at n₁ = n₂ in the benchmark data.

     Strategy:
     1. Generate container with power-of-2 sizes for systematic coverage
     2. Use worst-case keys (differ only in last 4 bytes)
     3. Select subset of container entries as contained (ensures no early exit)
     4. Test multiple contained sizes to explore the n₁ × n₂ space

     Result: ~1000 systematic worst-case benchmarks
  -}

  let containerSizes = [2 ^ n | n <- [1 .. 10 :: Int]] -- [2, 4, ..., 1024]

  -- Generate test cases for all container size combinations
  concat
    <$> sequence
      [ do
          -- Generate container with worst-case BST structure:
          -- - Uniform distribution (all policies have same token count)
          -- - Worst-case keys (long common prefix, differ in last 4 bytes)
          (container, _, _) <-
            generateConstrainedValueWithMaxPolicy numPolicies tokensPerPolicy g

          -- Extract all entries from container as a flat list
          -- Selecting from container maintains subset relationship: contained ⊆ container
          let allEntries = Value.toFlatList container
              totalEntries = length allEntries

          -- Generate test cases for different contained sizes (uniform linear distribution)
          -- Each size tests the same container with different iteration counts
          let maxContainedSize = min 1000 totalEntries
              numSamples = 10
              containedSizes =
                if totalEntries < numSamples
                  then [1 .. totalEntries] -- Test all sizes for small containers
                  else
                    let step = maxContainedSize `div` numSamples
                     in [i * step | i <- [1 .. numSamples], i * step > 0]
                          ++ [maxContainedSize | maxContainedSize `notElem` [i * step | i <- [1 .. numSamples]]]

          -- Create one test case per contained size
          pure
            [ let
                selectedEntries = take containedSize allEntries
                contained =
                  unsafeFromBuiltinResult $
                    Value.fromList
                      [ (policyId, [(tokenName, quantity)])
                      | (policyId, tokenName, quantity) <- selectedEntries
                      ]
               in
                (container, contained)
            | containedSize <- containedSizes
            ]
      | numPolicies <- containerSizes
      , tokensPerPolicy <- containerSizes
      ]

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

-- | Generate Value with random number of entries between 1 and maxValueEntries
generateValue :: StatefulGen g m => g -> m Value
generateValue g = do
  numEntries <- uniformRM (1, maxValueEntries) g
  generateValueMaxEntries numEntries g

{-| Maximum number of (policyId, tokenName, quantity) entries for Value generation.
This represents the practical limit based on execution budget constraints.
Scripts can programmatically generate large Values, so we benchmark based on
what's achievable within CPU execution budget, not ledger storage limits.

Equivalent byte size: ~7.2 MB (100,000 × 72 bytes per entry where each entry
consists of: 32-byte policyId + 32-byte tokenName + 8-byte Int64 quantity) -}
maxValueEntries :: Int
maxValueEntries = 100_000

-- | Generate Value within total size budget
generateValueMaxEntries :: StatefulGen g m => Int -> g -> m Value
generateValueMaxEntries maxEntries g = do
  -- Uniform random distribution: cover full range from many policies (few tokens each)
  -- to few policies (many tokens each)
  numPolicies <- uniformRM (1, maxEntries) g
  let tokensPerPolicy = if numPolicies > 0 then maxEntries `div` numPolicies else 0

  generateConstrainedValue numPolicies tokensPerPolicy g

-- | Generate constrained Value with information about max-size policy
generateConstrainedValueWithMaxPolicy
  :: StatefulGen g m
  => Int -- Number of policies
  -> Int -- Number of tokens per policy
  -> g
  -> m (Value, K, K) -- Returns (value, maxPolicyId, deepestTokenInMaxPolicy)
generateConstrainedValueWithMaxPolicy numPolicies tokensPerPolicy g = do
  policyIds <- replicateM numPolicies (generateKey g)
  tokenNames <- replicateM tokensPerPolicy (generateKey g)

  let
    qty :: Value.Quantity
    qty = case Value.quantity (fromIntegral (maxBound :: Int64)) of
      Just q -> q
      Nothing -> error "generateConstrainedValueWithMaxPolicy: Int64 maxBound should be valid Quantity"

    -- Sort policy IDs to establish BST ordering
    sortedPolicyIds = sort policyIds

    -- Select the maximum policy ID (rightmost/deepest in BST) for worst-case outer lookup
    maxPolicyId = last sortedPolicyIds

    -- Sort token names to establish BST ordering within the max policy
    sortedTokenNames = sort tokenNames

    -- Select the maximum token (rightmost/deepest in inner BST) for worst-case inner lookup
    deepestToken = last sortedTokenNames

    -- Build nestedMap with optimized structure:
    -- 1. Max policy gets full token list (for worst-case inner BST depth)
    -- 2. All other policies get minimal (single-token) maps to minimize off-path cost
    nestedMap :: [(K, [(K, Value.Quantity)])]
    nestedMap =
      [ if policyId == maxPolicyId
          then (policyId, (,qty) <$> sortedTokenNames) -- Full map for max policy
          else (policyId, [(head sortedTokenNames, qty)]) -- Minimal map for others
      | policyId <- sortedPolicyIds
      ]

    value = unsafeFromBuiltinResult $ Value.fromList nestedMap

  pure (value, maxPolicyId, deepestToken)

-- | Generate constrained Value (legacy interface for other builtins)
generateConstrainedValue
  :: StatefulGen g m
  => Int -- Number of policies
  -> Int -- Number of tokens per policy
  -> g
  -> m Value
generateConstrainedValue numPolicies tokensPerPolicy g = do
  (value, _, _) <- generateConstrainedValueWithMaxPolicy numPolicies tokensPerPolicy g
  pure value

----------------------------------------------------------------------------------------------------
-- Other Generators --------------------------------------------------------------------------------

{-| Generate a worst-case key for benchmarking ByteString comparisons.

ByteString comparison is lexicographic and short-circuits on the first differing byte.
Random keys typically differ in the first 1-2 bytes, making comparisons artificially cheap.

For accurate worst-case costing, we generate keys with a common prefix (0xFF bytes) that
differ only in the last 4 bytes. This forces full-length comparisons during Map lookups,
providing conservative cost estimates for adversarial on-chain scenarios. -}
generateKey :: StatefulGen g m => g -> m K
generateKey g = do
  let prefixLen = Value.maxKeyLen - 4
      prefix = BS.replicate prefixLen (0xFF :: Word8)
  -- Generate 4 random bytes for the suffix
  suffix <- BS.pack <$> replicateM 4 (uniformRM (0, 255) g)
  case Value.k (prefix <> suffix) of
    Just key -> pure key
    Nothing -> error "Internal error: maxKeyLen key should always be valid"

----------------------------------------------------------------------------------------------------
-- Helper Functions --------------------------------------------------------------------------------

{-| Extract value from BuiltinResult for benchmark data generation.

This function is intended for use in test and benchmark code where BuiltinResult
failures indicate bugs in the generator code, not runtime errors.

Errors if BuiltinResult indicates failure (should never happen with valid inputs).
The call stack will provide context about where the error occurred. -}
unsafeFromBuiltinResult :: HasCallStack => BuiltinResult a -> a
unsafeFromBuiltinResult = \case
  BuiltinSuccess x -> x
  BuiltinSuccessWithLogs _ x -> x
  BuiltinFailure _ err -> error $ "BuiltinResult failed: " <> show err
