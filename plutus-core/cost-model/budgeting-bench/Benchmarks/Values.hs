{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE NumericUnderscores  #-}

module Benchmarks.Values (makeBenchmarks) where

import Prelude

import Common
import Control.Monad (replicateM)
import Criterion.Main (Benchmark)
import Data.ByteString (ByteString)
import PlutusCore (DefaultFun (LookupCoin, UnValueData, ValueContains, ValueData))
import PlutusCore.Evaluation.Machine.ExMemoryUsage (Logarithmic (..), ValueOuterOrMaxInner (..),
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
    (id, id, Logarithmic . ValueOuterOrMaxInner) -- Wrap Value argument to report outer/max inner size
    LookupCoin -- the builtin fun
    [] -- no type arguments needed (monomorphic builtin)
    (lookupCoinArgs gen) -- the argument combos to generate benchmarks for

lookupCoinArgs :: StdGen -> [(ByteString, ByteString, Value)]
lookupCoinArgs gen = runStateGen_ gen $ \(g :: g) -> do
  -- Add search keys to common test values
  let testValues = generateTestValues gen
  commonWithKeys <- mapM (withSearchKeys g . pure) testValues

  -- Additional tests specific to lookupCoin
  let valueSizes = [(100, 10), (500, 20), (1_000, 50), (2_000, 100)]
  additionalTests <-
    sequence $
      concat
        [ -- Value size tests (number of policies × tokens per policy)
          [ generateLookupTest g numPolicies tokensPerPolicy
          | (numPolicies, tokensPerPolicy) <- valueSizes
          ]
        , -- Budget-constrained tests (at 30KB limit)
          [generateBudgetTest g 30_000]
        , -- Additional random tests for parameter spread
          replicate 50 (generateRandomLookupTest g)
        ]

  pure $ commonWithKeys ++ additionalTests

-- | Add random search keys to a Value (keys may or may not exist in the Value)
withSearchKeys :: (StatefulGen g m) => g -> m Value -> m (ByteString, ByteString, Value)
withSearchKeys g genValue = do
  value <- genValue
  key1 <- generateKeyBS g
  key2 <- generateKeyBS g
  pure (key1, key2, value)

-- | Generate lookup test with specified parameters
generateLookupTest
  :: (StatefulGen g m)
  => g
  -> Int -- Number of policies
  -> Int -- Tokens per policy
  -> m (ByteString, ByteString, Value)
generateLookupTest g numPolicies tokensPerPolicy =
  withSearchKeys g (generateConstrainedValue numPolicies tokensPerPolicy g)

-- | Generate budget-constrained test
generateBudgetTest
  :: (StatefulGen g m)
  => g
  -> Int -- Total budget
  -> m (ByteString, ByteString, Value)
generateBudgetTest g budget =
  withSearchKeys g (generateValueWithBudget budget g)

-- | Generate random lookup test with varied parameters for better spread
generateRandomLookupTest :: (StatefulGen g m) => g -> m (ByteString, ByteString, Value)
generateRandomLookupTest g = do
  numPolicies <- uniformRM (1, 2_000) g
  tokensPerPolicy <- uniformRM (1, 1_000) g
  withSearchKeys g (generateConstrainedValue numPolicies tokensPerPolicy g)

----------------------------------------------------------------------------------------------------
-- ValueContains -----------------------------------------------------------------------------------

valueContainsBenchmark :: StdGen -> Benchmark
valueContainsBenchmark gen =
  createTwoTermBuiltinBenchElementwiseWithWrappers
    (Logarithmic . ValueOuterOrMaxInner, ValueTotalSize)
    -- Container: outer/maxInner, Contained: totalSize
    ValueContains -- the builtin fun
    [] -- no type arguments needed (monomorphic builtin)
    (valueContainsArgs gen) -- the argument combos to generate benchmarks for

valueContainsArgs :: StdGen -> [(Value, Value)]
valueContainsArgs gen = runStateGen_ gen \g -> do
  let baseValueSizes = [1, 10, 100, 1_000]
  sequence $
    concat
      [ -- Value size tests with varying sizes
        [ generateContainsTest g containerSize containedSize
        | containerSize <- baseValueSizes
        , containedSize <- baseValueSizes
        , containedSize <= containerSize
        ]
      , -- Budget-constrained tests
        [generateContainsBudgetTest g 30_000]
      , -- Edge cases
        [ generateEmptyContainedTest g containerSize
        | containerSize <- [0, 10, 100, 1_000]
        ]
      , -- Random tests for parameter spread (100 combinations)
        replicate 100 (generateRandomContainsTest g)
      ]

-- | Generate valueContains test with specified parameters
generateContainsTest
  :: (StatefulGen g m)
  => g
  -> Int -- Container value size (number of policies)
  -> Int -- Contained value size (number of policies)
  -> m (Value, Value)
generateContainsTest g containerSize containedSize = do
  -- Generate container value
  container <- generateConstrainedValue containerSize 10 g

  -- Generate contained as subset of container (for true contains relationship)
  let containerList = Value.toList container
      containedEntries = take containedSize containerList

  let contained =
        Value.fromList $
          [ (policyId, take (containedSize `div` max 1 (length containerList)) tokens)
          | (policyId, tokens) <- containedEntries
          ]

  pure (container, contained)

-- | Generate budget-constrained contains test
generateContainsBudgetTest
  :: (StatefulGen g m)
  => g
  -> Int -- Total budget
  -> m (Value, Value)
generateContainsBudgetTest g budget = do
  container <- generateValueWithBudget budget g
  -- Generate smaller contained value (subset)
  let containerList = Value.toList container
      containedEntries = take (length containerList `div` 2) containerList
  pure (container, Value.fromList containedEntries)

-- | Generate test with empty contained value
generateEmptyContainedTest
  :: (StatefulGen g m)
  => g
  -> Int -- Container size (number of policies)
  -> m (Value, Value)
generateEmptyContainedTest g containerSize = do
  container <- generateConstrainedValue containerSize 10 g
  pure (container, Value.empty)

-- | Generate random valueContains test with varied parameters for better spread
generateRandomContainsTest :: (StatefulGen g m) => g -> m (Value, Value)
generateRandomContainsTest g = do
  -- Generate random parameters with good spread
  containerEntries <- uniformRM (1, 5_000) g -- 1-5000 container entries
  containedEntries <- uniformRM (1, containerEntries) g -- 1-container count

  -- Generate container value (1 token per policy for flat structure)
  container <- generateConstrainedValue containerEntries 1 g

  -- Generate contained as subset of container entries
  let containerList = Value.toList container
      containedList = take containedEntries containerList
      contained = Value.fromList containedList

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
generateTestValues gen = runStateGen_ gen \g -> do
  let
    baseValueSizes = [1, 10, 50, 100, 500, 1_000]

  sequence $
    concat
      [ -- Empty value as edge case
        [pure Value.empty]
      , -- Standard value sizes
        [ generateConstrainedValue numPolicies 10 g
        | numPolicies <- baseValueSizes
        ]
      , -- Budget-constrained tests
        [ generateValueWithBudget budget g
        | budget <- [1_000, 10_000, 30_000]
        ]
      , -- Random tests for parameter spread (50 combinations)
        replicate 50 $ do
          numPolicies <- uniformRM (1, 1_000) g
          tokensPerPolicy <- uniformRM (1, 500) g
          generateConstrainedValue numPolicies tokensPerPolicy g
      ]

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

  -- Generate positive quantities (1 to 1000000)
  let quantity :: Int -> Int -> Integer
      quantity policyIndex tokenIndex =
        fromIntegral (1 + (policyIndex * 1_000 + tokenIndex) `mod` 1_000_000)

      nestedMap :: [(K, [(K, Integer)])]
      nestedMap =
        [ ( policyId
          , [ (tokenName, quantity policyIndex tokenIndex)
            | (tokenIndex, tokenName) <- zip [0 ..] tokenNames
            ]
          )
        | (policyIndex, policyId) <- zip [0 ..] policyIds
        ]
  pure $ Value.fromList nestedMap

-- | Generate Value within total size budget
generateValueWithBudget
  :: (StatefulGen g m)
  => Int -- Target total size budget
  -> g
  -> m Value
generateValueWithBudget budget g = do
  let
    keySize = Value.maxKeyLen
    overhead = 8 -- bytes per amount

    -- Calculate maximum possible entries with fixed key sizes
    bytesPerEntry = keySize + keySize + overhead  -- policy + token + amount
    maxEntries = budget `div` bytesPerEntry

    -- Simple distribution: try to balance policies and tokens
    numPolicies = max 1 (floor (sqrt (fromIntegral maxEntries :: Double)))
    tokensPerPolicy = if numPolicies > 0 then maxEntries `div` numPolicies else 0

  generateConstrainedValue numPolicies tokensPerPolicy g

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
