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
import Control.Monad.State.Strict (State)
import Criterion.Main (Benchmark)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Int (Int64)
import Data.List (find, sort)
import Data.Map.Strict qualified as Map
import Data.Word (Word8)
import GHC.Stack (HasCallStack)
import PlutusCore (DefaultFun (InsertCoin, LookupCoin, ScaleValue, UnValueData, UnionValue, ValueContains, ValueData))
import PlutusCore.Builtin (BuiltinResult (BuiltinFailure, BuiltinSuccess, BuiltinSuccessWithLogs))

import PlutusCore.Evaluation.Machine.ExMemoryUsage
  ( DataNodeCount (..)
  , ValueMaxDepth (..)
  , ValueTotalSize (..)
  )
import PlutusCore.Value
  ( K
  , Quantity (..)
  , Value
  )
import PlutusCore.Value qualified as Value

import System.Random.Stateful
  ( StateGenM
  , StatefulGen
  , StdGen
  , runStateGen_
  , uniformRM
  )

----------------------------------------------------------------------------------------------------
-- Benchmarks --------------------------------------------------------------------------------------

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen =
  [ lookupCoinBenchmark gen
  , valueContainsBenchmark gen
  , valueDataBenchmark gen
  , unValueDataBenchmark gen
  , insertCoinBenchmark gen
  , unionValueBenchmark gen
  , scaleValueBenchmark gen
  ]

----------------------------------------------------------------------------------------------------
-- LookupCoin --------------------------------------------------------------------------------------

lookupCoinBenchmark :: StdGen -> Benchmark
lookupCoinBenchmark gen =
  createThreeTermBuiltinBenchElementwiseWithWrappers
    (id, id, ValueMaxDepth) -- Wrap Value argument to report sum of log sizes
    LookupCoin -- the builtin fun
    [] -- no type arguments needed (monomorphic builtin)
    (runBenchGen gen lookupCoinArgs) -- the argument combos to generate benchmarks for

lookupCoinArgs :: StatefulGen g m => g -> m [(ByteString, ByteString, Value)]
lookupCoinArgs gen = do
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
    [ withWorstCaseSearchKeys (generateConstrainedValueWithMaxPolicy numPolicies tokensPerPolicy gen)
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
    -- Both use ValueTotalSize for meaningful diagonal comparison:
    -- when contained size > container size, containment is impossible
    ValueContains -- the builtin fun
    [] -- no type arguments needed (monomorphic builtin)
    (valueContainsArgs gen) -- the argument combos to generate benchmarks for

valueContainsArgs :: StdGen -> [(Value, Value)]
valueContainsArgs gen = runStateGen_ gen \g -> do
  {- ValueContains performs multiple LookupCoin operations (one per entry in
     contained). Worst case: All lookups succeed at maximum depth with many
     entries to check.

     Strategy:
     1. Generate container with worst-case BST structure (power-of-2 sizes)
     2. Sample below-diagonal in (numPolicies, tokensPerPolicy) space to
        reduce clustering at small sizes
     3. Select entries FROM container (maintain subset relationship)
     4. Include deepest entry to force maximum BST traversal
     5. Add true above-diagonal samples where contained size > container size

     NOTE: Two different "diagonal" concepts:
     - Value structure diagonal: numPolicies vs tokensPerPolicy (map shape)
     - Costing diagonal: container totalSize vs contained totalSize
       (used by const_above_diagonal cost model)

     Size calculation: containerSize = tokensPerPolicy + (numPolicies - 1)
     Max size: 1024 + 1023 = 2047 (symmetric with LookupCoin range)

     Grid: 10×10 power-of-2 below-diagonal (55 combos)
     Samples per container: 10 evenly distributed contained sizes
     Above-diagonal: 20 independent (container, contained) pairs
     Total points: ~570
  -}

  let containerSizes = [2 ^ n | n <- [1 .. 10 :: Int]]

      -- Value structure combinations: numPolicies >= tokensPerPolicy
      -- Focuses on typical case (more policies than tokens per policy)
      -- Reduces clustering at small sizes (55 of 100 combinations)
      structureCombos = [(p, t) | p <- containerSizes, t <- containerSizes, p >= t]

  -- Below-diagonal samples: contained is subset of container
  belowDiagonalSamples <-
    concat
      <$> sequence
        [ do
            (container, maxPolicyId, deepestToken) <-
              generateConstrainedValueWithMaxPolicy numPolicies tokensPerPolicy g

            let allEntries = Value.toFlatList container
                totalEntries = length allEntries
                worstCaseEntry = find (\(p, t, _) -> p == maxPolicyId && t == deepestToken) allEntries

            -- Generate evenly distributed contained sizes
            let maxContainedSize = totalEntries
                numSamples = 10
                containedSizes =
                  if totalEntries < numSamples
                    then [1 .. totalEntries]
                    else
                      let step = maxContainedSize `div` numSamples
                       in [i * step | i <- [1 .. numSamples], i * step > 0]
                            ++ [ maxContainedSize
                               | maxContainedSize `notElem` [i * step | i <- [1 .. numSamples]]
                               ]

            pure
              [ let
                  selectedEntries =
                    case worstCaseEntry of
                      Nothing -> take containedSize allEntries
                      Just worst ->
                        let allEntriesWithoutWorst = filter (/= worst) allEntries
                            numOthers = min (containedSize - 1) (totalEntries - 1)
                            others = take numOthers allEntriesWithoutWorst
                         in others ++ [worst]

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
        | (numPolicies, tokensPerPolicy) <- structureCombos
        ]

  -- Above-diagonal samples: contained size > container size
  -- Tests constant-cost early-exit path (containment impossible)
  -- 20 samples with varied container/contained size ratios
  aboveDiagonalSamples <-
    sequence
      [ do
          -- Generate smaller container
          container <- generateConstrainedValue smallP smallT g
          -- Generate larger contained (independent, not a subset)
          contained <- generateConstrainedValue largeP largeT g
          pure (container, contained)
      | (smallP, smallT, largeP, largeT) <-
          -- Small containers with various larger contained sizes
          [ (2, 2, 4, 4) -- container ~4, contained ~16
          , (2, 3, 8, 8) -- container ~6, contained ~64
          , (2, 5, 10, 10) -- container ~10, contained ~100
          , (3, 3, 10, 10) -- container ~9, contained ~100
          , (4, 4, 16, 16) -- container ~16, contained ~256
          -- Medium containers with larger contained sizes
          , (5, 5, 20, 20) -- container ~25, contained ~400
          , (5, 10, 20, 20) -- container ~50, contained ~400
          , (8, 8, 32, 32) -- container ~64, contained ~1024
          , (10, 5, 30, 30) -- container ~50, contained ~900
          , (10, 10, 40, 40) -- container ~100, contained ~1600
          -- Larger containers with much larger contained sizes
          , (10, 10, 50, 20) -- container ~100, contained ~1000
          , (15, 10, 50, 50) -- container ~150, contained ~2500
          , (20, 10, 60, 60) -- container ~200, contained ~3600
          , (20, 20, 80, 80) -- container ~400, contained ~6400
          , (30, 15, 100, 50) -- container ~450, contained ~5000
          -- Very large containers with extreme contained sizes
          , (40, 20, 120, 80) -- container ~800, contained ~9600
          , (50, 20, 150, 100) -- container ~1000, contained ~15000
          , (64, 16, 128, 128) -- container ~1024, contained ~16384
          , (100, 10, 200, 100) -- container ~1000, contained ~20000
          , (128, 8, 256, 64) -- container ~1024, contained ~16384
          ]
      ]

  pure (belowDiagonalSamples ++ aboveDiagonalSamples)

----------------------------------------------------------------------------------------------------
-- ValueData
-- ---------------------------------------------------------------------------------------
-- We use the `nf` benchmark version here because `valueData` returns an object
-- of the form `Map . ...` and `whnf` won't evaluate anything under `Map`.
valueDataBenchmark :: StdGen -> Benchmark
valueDataBenchmark gen =
  createOneTermBuiltinBenchWithWrapper_NF
    ValueTotalSize
    ValueData
    []
    (generateTestValues gen)

----------------------------------------------------------------------------------------------------
-- UnValueData -------------------------------------------------------------------------------------

-- Benchmarks for `unValueData :: Data -> Value`.  We generate random values,
-- convert them to the corresponding `data` objects, and use these as inputs to
-- `unValueData`.  Each `data` objects is a list of `(currencyId, innerMap)`
-- pairs and each `innerMap` is a list of `(tokenId, quantity)` pairs.  Both of
-- these will be ordered in ascending order of their keys, which is the
-- best-case input to Map.fromListWith, which is used in the implementation of
-- `unValueData`.  We reverse the lists to make the inputs less favourable (and
-- possibly worst-case).
unValueDataBenchmark :: StdGen -> Benchmark
unValueDataBenchmark gen =
  createOneTermBuiltinBenchWithWrapper
    DataNodeCount
    UnValueData
    []
    ((unsafeFromBuiltinResult . Value.valueData) <$> generateTestValues gen)

-- FIXME: account properly for out-of-range errors when test values are too big.

----------------------------------------------------------------------------------------------------
-- InsertCoin --------------------------------------------------------------------------------------

insertCoinBenchmark :: StdGen -> Benchmark
insertCoinBenchmark gen =
  createFourTermBuiltinBenchElementwiseWithWrappers
    (id, id, id, ValueMaxDepth)
    InsertCoin
    []
    (runBenchGen gen insertCoinArgs)

insertCoinArgs :: StatefulGen g m => g -> m [(ByteString, ByteString, Integer, Value)]
insertCoinArgs gen = do
  lookupArgs <- lookupCoinArgs gen
  let noOfBenches = length lookupArgs
  amounts <- genZeroOrMaxAmount gen noOfBenches
  pure $ reorderArgs <$> zip lookupArgs amounts
  where
    reorderArgs ((b1, b2, val), am) = (b1, b2, am, val)

----------------------------------------------------------------------------------------------------
-- UnionValue --------------------------------------------------------------------------------------

unionValueBenchmark :: StdGen -> Benchmark
unionValueBenchmark gen =
  createTwoTermBuiltinBenchElementwiseWithWrappers
    (ValueTotalSize, ValueTotalSize)
    UnionValue
    []
    (runBenchGen gen unionValueArgs)

{-| Maximum total size of Value arguments for UnionValue benchmarking.
Based on practical limits within execution budget constraints. -}
maxUnionValueEntries :: Int
maxUnionValueEntries = 50_000

{-| Generate argument pairs for UnionValue benchmarking.
The worst case is when both Values share as many keys as possible,
therefore we consider two Values where the first is a sub-value of the second.
Experiments have also shown that the worst case execution time for UnionValue
occurs for flat maps with a single token name per policy ID.
Therefore, we fix the number of token names to 1 for both Values. -}
unionValueArgs :: StatefulGen g m => g -> m [(Value, Value)]
unionValueArgs gen = replicateM 200 $ do
  numPolicyIdsV2 <- uniformRM (1, maxUnionValueEntries) gen
  policyIdsV2 <- replicateM numPolicyIdsV2 (generateKey gen)
  tokenName <- generateKey gen
  let amt = unQuantity (maxBound :: Quantity) `div` 2
      value2 = buildValue policyIdsV2 [tokenName] (mkQuantity amt)
  numPolicyIdsToKeep <- uniformRM (1, numPolicyIdsV2) gen
  let policyIdsV1 = take numPolicyIdsToKeep policyIdsV2
      value1 = buildValue policyIdsV1 [tokenName] (mkQuantity amt)
  pure (value1, value2)

----------------------------------------------------------------------------------------------------
-- ScaleValue --------------------------------------------------------------------------------------

scaleValueBenchmark :: StdGen -> Benchmark
scaleValueBenchmark gen =
  createTwoTermBuiltinBenchElementwiseWithWrappers
    (id, ValueTotalSize)
    ScaleValue
    []
    (runBenchGen gen scaleValueArgs)

{-| Maximum total size of Value arguments for ScaleValue benchmarking.
Based on practical limits within execution budget constraints. -}
maxScaleValueEntries :: Int
maxScaleValueEntries = 90_000

{-| Generate argument pairs for ScaleValue benchmarking.
Since 'scaleValue' needs to traverse the entire Value, we may fix the structure
of the Value to be a flattened map with a single token name per policy ID.
To ensure worst-case performance, we fix the resulting scaled quantities to
be 'maxBound'. -}
scaleValueArgs :: StatefulGen g m => g -> m [(Integer, Value)]
scaleValueArgs gen = replicateM 200 $ do
  numPolicyIds <- uniformRM (1, maxScaleValueEntries) gen
  policyIds <- replicateM numPolicyIds (generateKey gen)
  tokenName <- generateKey gen
  let scalar = unQuantity (maxBound :: Quantity) `div` 2
      amt = mkQuantity 2
      value = buildValue policyIds [tokenName] amt
  pure (scalar, value)

----------------------------------------------------------------------------------------------------
-- Value Generators --------------------------------------------------------------------------------

{-| Build Value from given policy IDs, token names and and a single quantity
for each (policy ID, token name) pair.
Uses 'unsafeFromList' because 'generateKey' may generate duplicate keys, although
it is unlikely it generates more than a few duplicates per run. -}
buildValue :: [K] -> [K] -> Quantity -> Value
buildValue policyIds tokenNames amt =
  unsafeFromList entries
  where
    entries =
      [ ( pId
        , [ (tName, amt)
          | tName <- tokenNames
          ]
        )
      | pId <- policyIds
      ]

-- Number of benchmarking inputs for `valueData` and `unValueData`.
maxValueEntries :: Int
maxValueEntries = 50_000

-- | Test values for benchmarking `valueData` and `unValueData`
generateTestValues :: StdGen -> [Value]
generateTestValues gen = runStateGen_ gen \g ->
  -- Empty value as edge case
  (Value.empty :)
    <$>
    -- Random tests for parameter spread (100 combinations)
    replicateM 100 (generateValue g)
  where
    -- \| Generate Value with random number of entries between 1 and maxValueEntries
    generateValue :: StatefulGen g m => g -> m Value
    generateValue g = do
      numEntries <- uniformRM (1, maxValueEntries) g
      generateValueMaxEntries numEntries g

    -- \| Generate Value within total size budget
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

-- | Generate either zero or maximum amount Integer values, the probability of each is 50%
genZeroOrMaxAmount
  :: StatefulGen g m
  => g
  -> Int
  -- ^ Number of amounts to generate
  -> m [Integer]
genZeroOrMaxAmount gen n =
  genZeroOrAmount gen n (maxBound :: Quantity)

genZeroOrAmount
  :: StatefulGen g m
  => g
  -> Int
  -- ^ Number of amounts to generate
  -> Quantity
  -> m [Integer]
genZeroOrAmount gen n qty =
  replicateM n $ do
    coinType <- uniformRM (0 :: Int, 1) gen
    pure $ case coinType of
      0 -> 0
      1 -> unQuantity qty
      _ -> error "genZeroOrAmount: impossible"

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

-- | Abstracted runner for computations using stateful random generator 'StdGen'
runBenchGen :: StdGen -> (StateGenM StdGen -> State StdGen a) -> a
runBenchGen gen ma = runStateGen_ gen \g -> ma g

mkQuantity :: Integer -> Value.Quantity
mkQuantity qty = case Value.quantity qty of
  Just q -> q
  Nothing -> error "mkQuantity: out of bounds user supplied integer as quantity"

-- | Left biased unsafe fromList.
unsafeFromList :: [(K, [(K, Quantity)])] -> Value
unsafeFromList xs = Value.pack $ Map.fromList $ fmap Map.fromList <$> xs
