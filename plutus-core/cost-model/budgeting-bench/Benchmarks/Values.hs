{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE NumericUnderscores  #-}

module Benchmarks.Values (makeBenchmarks) where

import Prelude

import Common
import Control.Monad (replicateM)
import Control.Monad.State.Strict (State)
import Criterion.Main (Benchmark)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import PlutusCore (DefaultFun (LookupCoin, UnValueData, ValueContains, ValueData))
import PlutusCore.Evaluation.Machine.ExMemoryUsage (ValueOuterOrMaxInner (..), ValueTotalSize (..))
import PlutusCore.Value (Value)
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
    (id, id, ValueOuterOrMaxInner) -- Wrap Value argument to report outer/max inner size
    LookupCoin -- the builtin fun
    [] -- no type arguments needed (monomorphic builtin)
    (lookupCoinArgs gen) -- the argument combos to generate benchmarks for

lookupCoinArgs :: StdGen -> [(ByteString, ByteString, Value)]
lookupCoinArgs gen = runStateGen_ gen $ \(g :: g) -> do
  let
    -- Use common test values and add search keys
    testValues = generateTestValues gen

    -- Also include additional random tests specific to lookupCoin
    additionalTests = runStateGen_ gen $ \g' -> do
      let keySizes = [0, 1, 30, 100, 1_000, 10_000, 20_000]
      sequence $
        concat
          [ -- Key size impact tests with large keys
            [ generateLookupTest g' policySize tokenSize 100 10
            | policySize <- keySizes
            , tokenSize <- [0, 30, 1_000, 20_000]
            ]
          , -- Budget-constrained tests (at 30KB limit)
            [ generateBudgetTest g' policySize tokenSize 30_000
            | (policySize, tokenSize) <-
                [ (20_000, 1) -- Huge policy, tiny token
                , (1, 20_000) -- Tiny policy, huge token
                , (10_000, 10_000) -- Both large
                , (1, 1) -- Both tiny (max entries)
                , (0, 0) -- Empty keys (pathological)
                ]
            ]
          , -- Additional random tests for parameter spread
            replicate 50 (generateRandomLookupTest g')
          ]

    -- Add search keys to common test values

    -- Add search keys to a value for lookup testing
    -- Generates random keys that may or may not exist in the value
    addSearchKeysToValue :: Value -> State StdGen (ByteString, ByteString, Value)
    addSearchKeysToValue value = do
      -- Generate search keys with varying sizes (mostly 30 bytes for consistency)
      let keySize = 30 -- Standard key size used in most tests
      searchPolicyId <- generatePolicyId keySize g
      searchTokenName <- generateTokenName keySize g
      pure (searchPolicyId, searchTokenName, value)

  commonWithKeys <- sequence [addSearchKeysToValue value | value <- testValues]

  pure $ commonWithKeys ++ additionalTests

-- | Generate lookup test with specified parameters
generateLookupTest
  :: (StatefulGen g m)
  => g
  -> Int -- Policy ID byte size
  -> Int -- Token name byte size
  -> Int -- Number of policies
  -> Int -- Tokens per policy
  -> m (ByteString, ByteString, Value)
generateLookupTest
  g
  policyIdBytes
  tokenNameBytes
  numPolicies
  tokensPerPolicy = do
    value <-
      generateConstrainedValue
        numPolicies
        tokensPerPolicy
        policyIdBytes
        tokenNameBytes
        g
    -- Generate lookup keys (may or may not exist in value)
    searchPolicyId <- generatePolicyId policyIdBytes g
    searchTokenName <- generateTokenName tokenNameBytes g
    pure (searchPolicyId, searchTokenName, value)

-- | Generate budget-constrained test
generateBudgetTest
  :: (StatefulGen g m)
  => g
  -> Int -- Policy ID byte size
  -> Int -- Token name byte size
  -> Int -- Total budget
  -> m (ByteString, ByteString, Value)
generateBudgetTest g policyIdBytes tokenNameBytes budget = do
  value <- generateValueWithBudget policyIdBytes tokenNameBytes budget g
  searchPolicyId <- generatePolicyId policyIdBytes g
  searchTokenName <- generateTokenName tokenNameBytes g
  pure (searchPolicyId, searchTokenName, value)

-- | Generate random lookup test with varied parameters for better spread
generateRandomLookupTest :: (StatefulGen g m) => g -> m (ByteString, ByteString, Value)
generateRandomLookupTest g = do
  policyIdBytes <- uniformRM (0, 20_000) g -- 0-20KB policy ID
  tokenNameBytes <- uniformRM (0, 20_000) g -- 0-20KB token name
  numPolicies <- uniformRM (1, 2_000) g -- 1-2000 policies
  tokensPerPolicy <- uniformRM (1, 1_000) g -- 1-1000 tokens per policy

  -- Generate value with random parameters
  value <- generateConstrainedValue numPolicies tokensPerPolicy policyIdBytes tokenNameBytes g

  -- Generate search keys
  searchPolicyId <- uniformByteStringM policyIdBytes g
  searchTokenName <- uniformByteStringM tokenNameBytes g

  pure (searchPolicyId, searchTokenName, value)

----------------------------------------------------------------------------------------------------
-- ValueContains -----------------------------------------------------------------------------------

valueContainsBenchmark :: StdGen -> Benchmark
valueContainsBenchmark gen =
  createTwoTermBuiltinBenchElementwiseWithWrappers
    (ValueOuterOrMaxInner, ValueTotalSize)
    -- Container: outer/maxInner, Contained: totalSize
    ValueContains -- the builtin fun
    [] -- no type arguments needed (monomorphic builtin)
    (valueContainsArgs gen) -- the argument combos to generate benchmarks for

valueContainsArgs :: StdGen -> [(Value, Value)]
valueContainsArgs gen = runStateGen_ gen \g -> do
  let
    baseKeySizes = [0, 30, 1_000, 10_000]
    baseValueSizes = [1, 10, 100, 1_000]

  sequence $
    concat
      [ -- Standard key tests with varying value sizes (original Size-based tests)
        [ generateContainsTest g containerSize containedSize 30
        | containerSize <- baseValueSizes
        , containedSize <- baseValueSizes
        , containedSize <= containerSize
        ]
      , -- Key size impact tests
        [ generateContainsTest g 100 10 keySize
        | keySize <- baseKeySizes
        ]
      , -- Budget-constrained tests
        [ generateContainsBudgetTest g 30_000 keySize
        | keySize <- [0, 30, 3_000, 20_000]
        ]
      , -- Edge cases
        [ generateEmptyContainedTest g containerSize 30
        | containerSize <- [0, 10, 100, 1_000]
        ]
      , -- Random tests for parameter spread (100 combinations)
        replicate 100 (generateRandomContainsTest g)
      ]

-- | Generate valueContains test with specified parameters
generateContainsTest
  :: (StatefulGen g m)
  => g
  -> Int -- Container value size
  -> Int -- Contained value size
  -> Int -- Key byte size (for both policy and token)
  -> m (Value, Value)
generateContainsTest g containerSize containedSize keySize = do
  -- Generate container value
  container <- generateConstrainedValue containerSize 10 keySize keySize g

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
  -> Int -- Key size
  -> m (Value, Value)
generateContainsBudgetTest g budget keySize = do
  container <- generateValueWithBudget keySize keySize budget g
  -- Generate smaller contained value (subset)
  let containerList = Value.toList container
      containedEntries = take (length containerList `div` 2) containerList
  pure (container, Value.fromList containedEntries)

-- | Generate test with empty contained value
generateEmptyContainedTest
  :: (StatefulGen g m)
  => g
  -> Int -- Container size
  -> Int -- Key size
  -> m (Value, Value)
generateEmptyContainedTest g containerSize keySize = do
  container <- generateConstrainedValue containerSize 10 keySize keySize g
  pure (container, Value.empty)

-- | Generate random valueContains test with varied parameters for better spread
generateRandomContainsTest :: (StatefulGen g m) => g -> m (Value, Value)
generateRandomContainsTest g = do
  -- Generate random parameters with good spread
  containerEntries <- uniformRM (1, 5_000) g -- 1-5000 container entries
  containedEntries <- uniformRM (1, containerEntries) g -- 1-container count
  keyBytes <- uniformRM (1, 5_000) g -- 1-5000 byte keys

  -- Generate container value with exact entry count
  container <- generateRandomValueForContains containerEntries keyBytes g

  -- Generate contained as subset of container entries
  let containerList = Value.toList container
      containedList = take containedEntries containerList
      contained = Value.fromList containedList

  pure (container, contained)

-- | Generate Value for contains tests with exact entry count
generateRandomValueForContains
  :: (StatefulGen g m)
  => Int -- Entry count
  -> Int -- Key byte size
  -> g
  -> m Value
generateRandomValueForContains entryCount keyBytes g = do
  -- Generate policies and tokens with exact entry count
  policyIds <- replicateM entryCount (uniformByteStringM keyBytes g)
  tokenNames <- replicateM entryCount (uniformByteStringM keyBytes g)

  let
    -- Create amounts (1 to 1000000)
    amounts = [fromIntegral (1 + i `mod` 1_000_000) | i <- [0 .. entryCount - 1]]

  pure $
    Value.fromList
      [ (policy, [(token, amount)])
      | (policy, token, amount) <- zip3 policyIds tokenNames amounts
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
generateTestValues gen = runStateGen_ gen \g -> do
  let
    baseValueSizes = [1, 10, 50, 100, 500, 1_000]
    keySizes = [0, 30, 100, 1_000, 10_000]

  sequence $
    concat
      [ -- Empty value as edge case (first test cbase)
        [pure Value.empty]
      , -- Standard value sizes with varying key sizes
        [ generateConstrainedValue valueSize 10 keySize keySize g
        | valueSize <- baseValueSizes
        , keySize <- [30, 1_000]
        ]
      , -- Key size impact tests (fixed value structure, varying key sizes)
        [ generateConstrainedValue 100 10 keySize keySize g
        | keySize <- keySizes
        ]
      , -- Budget-constrained tests
        [ generateValueWithBudget keySize keySize budget g
        | keySize <- [0, 30, 1_000, 10_000]
        , budget <- [1_000, 10_000, 30_000]
        ]
      , -- Random tests for parameter spread (50 combinations)
        replicate 50 $ do
          numPolicies <- uniformRM (1, 1_000) g
          tokensPerPolicy <- uniformRM (1, 500) g
          policyIdBytes <- uniformRM (0, 10_000) g
          tokenNameBytes <- uniformRM (0, 10_000) g
          generateConstrainedValue numPolicies tokensPerPolicy policyIdBytes tokenNameBytes g
      ]

-- | Generate constrained Value with total size budget
generateConstrainedValue
  :: (StatefulGen g m)
  => Int -- Number of policies
  -> Int -- Number of tokens per policy
  -> Int -- Policy ID byte length
  -> Int -- Token name byte length
  -> g
  -> m Value
generateConstrainedValue numPolicies tokensPerPolicy policyIdBytes tokenNameBytes g = do
  policyIds <- -- Generate policy IDs of specified size
    replicateM numPolicies (generatePolicyId policyIdBytes g)

  tokenNames <- -- Generate token names of specified size
    replicateM tokensPerPolicy (generateTokenName tokenNameBytes g)

  -- Generate positive quantities (1 to 1000000)
  let quantity :: Int -> Int -> Integer
      quantity policyIndex tokenIndex =
        fromIntegral (1 + (policyIndex * 1_000 + tokenIndex) `mod` 1_000_000)

      nestedMap :: [(ByteString, [(ByteString, Integer)])]
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
  => Int -- Policy ID byte length
  -> Int -- Token name byte length
  -> Int -- Target total size budget
  -> g
  -> m Value
generateValueWithBudget policyIdBytes tokenNameBytes budget g = do
  let
    overhead = 8 -- bytes per amount

    -- Calculate maximum possible entries
    bytesPerEntry = policyIdBytes + tokenNameBytes + overhead
    maxEntries =
      if bytesPerEntry > 0
        then min (budget `div` bytesPerEntry) budget
        else budget -- Handle 0 case

    -- Simple distribution: try to balance policies and tokens
    numPolicies = max 1 (floor (sqrt (fromIntegral maxEntries :: Double)))
    tokensPerPolicy = if numPolicies > 0 then maxEntries `div` numPolicies else 0

  generateConstrainedValue numPolicies tokensPerPolicy policyIdBytes tokenNameBytes g

----------------------------------------------------------------------------------------------------
-- Other Generators --------------------------------------------------------------------------------

-- | Generate policy ID of specified size
generatePolicyId :: (StatefulGen g m) => Int -> g -> m ByteString
generatePolicyId = generateByteString

-- | Generate token name of specified size
generateTokenName :: (StatefulGen g m) => Int -> g -> m ByteString
generateTokenName = generateByteString

-- | Generate ByteString of specified size
generateByteString :: (StatefulGen g m) => Int -> g -> m ByteString
generateByteString 0 _ = pure BS.empty
generateByteString l g = uniformByteStringM l g
