{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NumericUnderscores  #-}
{-# LANGUAGE TupleSections       #-}

module Benchmarks.Values (makeBenchmarks) where

import Prelude

import Common
import Control.Monad (replicateM)
import Criterion.Main (Benchmark)
import Data.Bits (shiftR, (.&.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Int (Int64)
import Data.Word (Word8)
import GHC.Stack (HasCallStack)
import PlutusCore (DefaultFun (LookupCoin, UnValueData, ValueContains, ValueData))
import PlutusCore.Builtin (BuiltinResult (BuiltinFailure, BuiltinSuccess, BuiltinSuccessWithLogs))
import PlutusCore.Evaluation.Machine.ExMemoryUsage (ValueLogOuterOrMaxInner (..),
                                                    ValueLogOuterSizeAddLogMaxInnerSize (..),
                                                    ValueTotalSize (..))
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
  -- Add worst-case search keys to common test values (filter out empty values)
  let testValues = filter (not . null . Value.toList) (generateTestValues gen)
      commonWithKeys = map (\v -> let (k1, k2) = extractWorstCaseKeys v in (k1, k2, v)) testValues

  {- Worst-case size combinations for BST lookup benchmarking.
     These test specific (policies, tokens) pairs chosen to:
     1. Cover depths 10-18 evenly (every 2-3 levels)
     2. Use balanced distributions to maximize nodes at each depth
     3. Test variety of skewed distributions per experimental findings

     | Combination  | log₂(outer) | log₂(inner) | Total Depth | Total Entries |
     |--------------|-------------|-------------|-------------|---------------|
     | (32, 32)     | 5           | 5           | 10          | 1,024         |
     | (64, 128)    | 6           | 7           | 13          | 8,192         |
     | (256, 256)   | 8           | 8           | 16          | 65,536        |
     | (512, 512)   | 9           | 9           | 18          | 262,144       |
     | (1024, 128)  | 10          | 7           | 17          | 131,072       |
     | (2048, 64)   | 11          | 6           | 17          | 131,072       |
  -}
  let valueSizes =
        [ (32, 32)     -- Balanced, depth 10
        , (64, 128)    -- Slight inner skew, depth 13
        , (256, 256)   -- Balanced, depth 16
        , (512, 512)   -- Balanced worst case, depth 18
        , (1024, 128)  -- Heavy outer skew, depth 17
        , (2048, 64)   -- Very heavy outer skew, depth 17
        ]
  additionalTests <-
    sequence $
      -- Value size tests (number of policies × tokens per policy)
      [ withWorstCaseSearchKeys (generateConstrainedValueWithMaxPolicy numPolicies tokensPerPolicy g)
      | (numPolicies, tokensPerPolicy) <- valueSizes
      ]
        -- Additional random tests for parameter spread with worst-case targeting
        <> replicate 100 (do
             value <- generateValue g
             pure $ let (k1, k2) = extractWorstCaseKeys value in (k1, k2, value))
  pure $ commonWithKeys ++ additionalTests

-- | Add worst-case search keys targeting the max-size inner map
withWorstCaseSearchKeys :: (Monad m) => m (Value, K, K) -> m (ByteString, ByteString, Value)
withWorstCaseSearchKeys genValueWithKeys = do
  (value, maxPolicyId, deepestToken) <- genValueWithKeys
  pure (Value.unK maxPolicyId, Value.unK deepestToken, value)

-- | Extract worst-case keys from an existing Value (for random values)
extractWorstCaseKeys :: Value -> (ByteString, ByteString)
extractWorstCaseKeys value =
  let valueList = Value.toList value
   in case valueList of
        [] -> error "extractWorstCaseKeys: empty value"
        _ ->
          -- Find the policy with the maximum number of tokens
          let (maxPolicy, maxTokens) =
                foldr1
                  ( \(p1, ts1) (p2, ts2) ->
                      if length ts1 >= length ts2 then (p1, ts1) else (p2, ts2)
                  )
                  valueList
              -- Get the last token in that policy (deepest in binary tree)
              deepestToken = case maxTokens of
                [] -> error "extractWorstCaseKeys: empty token list"
                _  -> fst (last maxTokens)
           in (Value.unK maxPolicy, Value.unK deepestToken)

----------------------------------------------------------------------------------------------------
-- ValueContains -----------------------------------------------------------------------------------

valueContainsBenchmark :: StdGen -> Benchmark
valueContainsBenchmark gen =
  createTwoTermBuiltinBenchElementwiseWithWrappers
    (ValueLogOuterOrMaxInner, ValueTotalSize)
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
        unsafeFromBuiltinResult $
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

-- | Generate constrained Value with information about max-size policy
generateConstrainedValueWithMaxPolicy
  :: (StatefulGen g m)
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
      Just q  -> q
      Nothing -> error "generateConstrainedValueWithMaxPolicy: Int64 maxBound should be valid Quantity"

    nestedMap :: [(K, [(K, Value.Quantity)])]
    nestedMap = (,(,qty) <$> tokenNames) <$> policyIds

    value = unsafeFromBuiltinResult $ Value.fromList nestedMap

    -- All policies have the same number of tokens in this uniform distribution,
    -- so we pick the first policy as the max-size policy for worst-case targeting
    maxPolicyId = head policyIds
    -- Pick the last token (deepest in binary search tree) for worst-case inner lookup
    deepestToken = last tokenNames

  pure (value, maxPolicyId, deepestToken)

-- | Generate constrained Value (legacy interface for other builtins)
generateConstrainedValue
  :: (StatefulGen g m)
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
differ only in the last bytes. This forces full-length comparisons during Map lookups,
providing conservative cost estimates for adversarial on-chain scenarios.

We use a random integer to ensure uniqueness while maintaining the worst-case prefix pattern.
-}
generateKey :: (StatefulGen g m) => g -> m K
generateKey g = do
  -- Generate a random integer for uniqueness
  n <- uniformRM (0, maxBound :: Int) g
  case Value.k (mkWorstCaseKey n) of
    Just key -> pure key
    Nothing  -> error "Internal error: maxKeyLen key should always be valid"

{-| Helper: Create a worst-case ByteString key from an integer
The key has maxKeyLen-4 bytes of 0xFF prefix, followed by 4 bytes encoding the integer
-}
mkWorstCaseKey :: Int -> ByteString
mkWorstCaseKey n =
  let prefixLen = Value.maxKeyLen - 4
      prefix = BS.replicate prefixLen (0xFF :: Word8)
      -- Encode the integer in big-endian format (last 4 bytes)
      b0 = fromIntegral $ (n `shiftR` 24) .&. 0xFF
      b1 = fromIntegral $ (n `shiftR` 16) .&. 0xFF
      b2 = fromIntegral $ (n `shiftR` 8) .&. 0xFF
      b3 = fromIntegral $ n .&. 0xFF
      suffix = BS.pack [b0, b1, b2, b3]
   in prefix <> suffix

----------------------------------------------------------------------------------------------------
-- Helper Functions --------------------------------------------------------------------------------

{-| Extract value from BuiltinResult for benchmark data generation.

This function is intended for use in test and benchmark code where BuiltinResult
failures indicate bugs in the generator code, not runtime errors.

Errors if BuiltinResult indicates failure (should never happen with valid inputs).
The call stack will provide context about where the error occurred.
-}
unsafeFromBuiltinResult :: (HasCallStack) => BuiltinResult a -> a
unsafeFromBuiltinResult = \case
  BuiltinSuccess x -> x
  BuiltinSuccessWithLogs _ x -> x
  BuiltinFailure _ err -> error $ "BuiltinResult failed: " <> show err
