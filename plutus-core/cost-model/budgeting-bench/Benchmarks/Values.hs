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
import Data.List (find, sort)
import Data.Word (Word8)
import GHC.Stack (HasCallStack)
import PlutusCore (DefaultFun (InsertCoin, LookupCoin, ScaleValue, UnValueData, UnionValue, ValueContains, ValueData))
import PlutusCore.Builtin (BuiltinResult (BuiltinFailure, BuiltinSuccess, BuiltinSuccessWithLogs))
import PlutusCore.Evaluation.Machine.ExMemoryUsage
  ( ValueLogOuterSizeAddLogMaxInnerSize (..)
  , ValueTotalSize (..)
  )
import PlutusCore.Value (K, Quantity (..), Value)
import PlutusCore.Value qualified as Value
import System.Random.Stateful (StateGenM, StatefulGen, StdGen, runStateGen_, uniformRM)

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
    (id, id, ValueLogOuterSizeAddLogMaxInnerSize) -- Wrap Value argument to report sum of log sizes
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
    (ValueLogOuterSizeAddLogMaxInnerSize, ValueTotalSize)
    -- Container: sum of log sizes, Contained: totalSize
    ValueContains -- the builtin fun
    [] -- no type arguments needed (monomorphic builtin)
    (valueContainsArgs gen) -- the argument combos to generate benchmarks for

valueContainsArgs :: StdGen -> [(Value, Value)]
valueContainsArgs gen = runStateGen_ gen \g -> do
  {- ValueContains performs multiple LookupCoin operations (one per entry in contained).
     Worst case: All lookups succeed at maximum depth with many entries to check.

     Strategy:
     1. Generate container with worst-case BST structure (uniform, power-of-2 sizes)
     2. Select entries FROM container (maintain subset relationship for no early exit)
     3. Include deepest entry to force maximum BST traversal
     4. Test multiple contained sizes to explore iteration count dimension

     Result: ~1000 systematic worst-case benchmarks vs 100 random cases previously
  -}

  -- Use power-of-2 grid (without half-powers) for systematic coverage
  -- ValueContains does multiple lookups, so we don't need as fine-grained
  -- size variation as LookupCoin
  let containerSizes = [2 ^ n | n <- [1 .. 10 :: Int]] -- [2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]

  -- Generate test cases for all container size combinations
  concat
    <$> sequence
      [ do
          -- Generate container with worst-case BST structure:
          -- - Uniform distribution (all policies have same token count)
          -- - Worst-case keys (long common prefix, differ in last 4 bytes)
          -- - Returns metadata about the deepest entry
          (container, maxPolicyId, deepestToken) <-
            generateConstrainedValueWithMaxPolicy numPolicies tokensPerPolicy g

          -- Extract all entries from container as a flat list
          -- This maintains the subset relationship: contained ⊆ container
          let allEntries = Value.toFlatList container
              totalEntries = length allEntries

          -- Find the worst-case entry (deepest in both BSTs)
          -- This entry forces maximum depth lookup:
          -- - maxPolicyId: first in outer BST (but all equal size, so any works)
          -- - deepestToken: last token in sorted order (maximum inner BST depth)
          let worstCaseEntry =
                find (\(p, t, _) -> p == maxPolicyId && t == deepestToken) allEntries

          -- Generate test cases for different contained sizes (uniform linear distribution)
          -- Each size tests the same container with different iteration counts
          -- Use uniform spacing from 1 to min(1000, totalEntries) for better distribution
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
                -- Select entries ensuring worst-case is included
                -- Place worst-case entry at END so it's checked (not early-exit)
                selectedEntries =
                  case worstCaseEntry of
                    Just worst ->
                      -- Take (containedSize - 1) entries, then add worst-case
                      -- This ensures: 1) subset relationship maintained
                      --               2) worst-case depth is hit
                      --               3) no early exit (all lookups succeed)
                      -- IMPORTANT: Filter out worst from allEntries first to prevent duplicates
                      -- (worst might be at a low position for small tokensPerPolicy values)
                      let allEntriesWithoutWorst = filter (/= worst) allEntries
                          numOthers = min (containedSize - 1) (totalEntries - 1)
                          others = take numOthers allEntriesWithoutWorst
                       in others ++ [worst]
                    Nothing ->
                      -- Fallback if worst-case entry somehow not found
                      -- (shouldn't happen, but defensive programming)
                      take containedSize allEntries

                -- Build contained Value from selected entries
                -- This maintains the Value structure while ensuring subset
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
-- InsertCoin --------------------------------------------------------------------------------------

insertCoinBenchmark :: StdGen -> Benchmark
insertCoinBenchmark gen =
  createFourTermBuiltinBenchElementwiseWithWrappers
    (id, id, id, ValueLogOuterSizeAddLogMaxInnerSize)
    InsertCoin
    []
    (runBenchGen gen insertCoinArgs)

insertCoinArgs :: StatefulGen g m => g -> m [(ByteString, ByteString, Integer, Value)]
insertCoinArgs gen = do
  lookupArgs <- lookupCoinArgs gen
  let noOfBenchs = length lookupArgs
  amounts <- genZeroOrMaxAmount gen noOfBenchs
  pure $ reorderArgs <$> zip lookupArgs amounts
  where
    reorderArgs ((b1, b2, val), am) = (b1, b2, am, val)

-- | Generate either zero or maximum amount Integer values, the probability of each is 50%
genZeroOrMaxAmount
  :: StatefulGen g m
  => g
  -> Int
  -- ^ Number of amounts to generate
  -> m [Integer]
genZeroOrMaxAmount gen n =
  replicateM n $ do
    coinType <- uniformRM (0 :: Int, 1) gen
    pure $ case coinType of
      0 -> 0
      1 -> unQuantity maxBound
      _ -> error "genZeroOrMaxAmount: impossible"

----------------------------------------------------------------------------------------------------
-- UnionValue --------------------------------------------------------------------------------------

unionValueBenchmark :: StdGen -> Benchmark
unionValueBenchmark gen =
  createTwoTermBuiltinBenchElementwiseWithWrappers
    (ValueTotalSize, ValueTotalSize)
    UnionValue
    []
    (runBenchGen gen unionValueArgs)

unionValueArgs :: StatefulGen g m => g -> m [(Value, Value)]
unionValueArgs gen = do
  vals1 <- replicateM 100 (generateValue gen)
  vals2 <- replicateM 100 (generateValue gen)
  pure $ zip vals1 vals2

----------------------------------------------------------------------------------------------------
-- ScaleValue --------------------------------------------------------------------------------------

scaleValueBenchmark :: StdGen -> Benchmark
scaleValueBenchmark gen =
  createTwoTermBuiltinBenchElementwiseWithWrappers
    (id, ValueTotalSize)
    ScaleValue
    []
    (runBenchGen gen scaleValueArgs)

scaleValueArgs :: StatefulGen g m => g -> m [(Integer, Value)]
scaleValueArgs gen = do
  let qty = mkQuantity . (floor :: Float -> Integer) . sqrt . fromInteger . unQuantity $ (maxBound :: Quantity)
  vals <- replicateM 100 (generateValueWithQuantity qty gen)
  scalars <- genZeroOrAmount gen 100 (qty - 1)
  pure $ zip scalars vals

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

-- | Generate Value with random number of entries between 1 and maxValueEntries
generateValueWithQuantity :: StatefulGen g m => Quantity -> g -> m Value
generateValueWithQuantity qty g = do
  numEntries <- uniformRM (1, maxValueEntries) g
  generateValueMaxEntriesWithQuantity numEntries qty g

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

generateValueMaxEntriesWithQuantity :: StatefulGen g m => Int -> Quantity -> g -> m Value
generateValueMaxEntriesWithQuantity maxEntries qty g = do
  -- Uniform random distribution: cover full range from many policies (few tokens each)
  -- to few policies (many tokens each)
  numPolicies <- uniformRM (1, maxEntries) g
  let tokensPerPolicy = if numPolicies > 0 then maxEntries `div` numPolicies else 0

  generateConstrainedValueWithQuantity numPolicies tokensPerPolicy qty g

-- | Generate constrained Value with information about max-size policy
generateConstrainedValueWithMaxPolicy
  :: StatefulGen g m
  => Int -- Number of policies
  -> Int -- Number of tokens per policy
  -> g
  -> m (Value, K, K) -- Returns (value, maxPolicyId, deepestTokenInMaxPolicy)
generateConstrainedValueWithMaxPolicy numPolicies tokensPerPolicy g =
  generateConstrainedValueWithMaxPolicyAndQuantity numPolicies tokensPerPolicy maxBound g

-- | Generate constrained Value with information about max-size policy and quantity
generateConstrainedValueWithMaxPolicyAndQuantity
  :: StatefulGen g m
  => Int -- Number of policies
  -> Int -- Number of tokens per policy
  -> Quantity -- Each token gets user defined quantity
  -> g
  -> m (Value, K, K) -- Returns (value, maxPolicyId, deepestTokenInMaxPolicy)
generateConstrainedValueWithMaxPolicyAndQuantity numPolicies tokensPerPolicy qty g = do
  policyIds <- replicateM numPolicies (generateKey g)
  tokenNames <- replicateM tokensPerPolicy (generateKey g)
  let
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

generateConstrainedValueWithQuantity
  :: StatefulGen g m
  => Int -- Number of policies
  -> Int -- Number of tokens per policy
  -> Quantity
  -> g
  -> m Value
generateConstrainedValueWithQuantity numPolicies tokensPerPolicy qty g = do
  (value, _, _) <- generateConstrainedValueWithMaxPolicyAndQuantity numPolicies tokensPerPolicy qty g
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
      _ -> error "genZeroOrMaxAmount: impossible"

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
      _ -> error "genZeroOrMaxAmount: impossible"

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
