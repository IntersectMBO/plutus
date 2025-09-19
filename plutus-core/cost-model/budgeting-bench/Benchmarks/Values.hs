{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE NumericUnderscores  #-}

module Benchmarks.Values (makeBenchmarks) where

import Prelude

import Common
import Control.Monad (replicateM)
import Criterion.Main (Benchmark)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import PlutusCore (DefaultFun (LookupCoin, ValueContains))
import PlutusCore.Value (Value)
import PlutusCore.Value qualified as Value
import System.Random.Stateful (StatefulGen, StdGen, runStateGen_, uniformByteStringM)

--------------------------------------------------------------------------------
-- Benchmarks ------------------------------------------------------------------

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen =
  [ createThreeTermBuiltinBenchElementwise
      LookupCoin -- the builtin fun
      [] -- no type arguments needed (monomorphic builtin)
      (lookupCoinArgs gen) -- the argument combos to generate benchmarks for
  , createTwoTermBuiltinBenchElementwise
      ValueContains -- the builtin fun
      [] -- no type arguments needed (monomorphic builtin)
      (valueContainsArgs gen) -- the argument combos to generate benchmarks for
  ]

lookupCoinArgs :: StdGen -> [(ByteString, ByteString, Value)]
lookupCoinArgs gen = runStateGen_ gen $ \g -> do
  let
    -- Key sizes to test (ByteString lengths)
    keySizes = [Size_0, Size_1, Size_30, Size_100, Size_1K, Size_10K, Size_20K]

  sequence $
    concat
      [ -- 1. Standard keys with varying value structures
        [ generateLookupTest g Size_30 Size_30 numPolicies tokensPerPolicy
        | numPolicies <- [Size_1, Size_10, Size_100, Size_1K]
        , tokensPerPolicy <- [Size_1, Size_10, Size_100]
        ]
      , -- 2. Key size impact tests (fixed structure, varying key sizes)
        [ generateLookupTest g pSize tSize Size_100 Size_10
        | pSize <- keySizes
        , tSize <- [Size_0, Size_30, Size_1K, Size_20K]
        ]
      , -- 3. Budget-constrained tests (at 30KB limit)
        [ generateBudgetTest g pSize tSize Size_30K
        | (pSize, tSize) <-
            [ (Size_20K, Size_1) -- Huge policy, tiny token
            , (Size_1, Size_20K) -- Tiny policy, huge token
            , (Size_10K, Size_10K) -- Both large
            , (Size_1, Size_1) -- Both tiny (max entries)
            , (Size_0, Size_0) -- Empty keys (pathological)
            ]
        ]
      , -- 4. Intermediate budget tests (at 10KB limit)
        [ generateBudgetTest g pSize tSize Size_10K
        | (pSize, tSize) <-
            [ (Size_100, Size_100)
            , (Size_1K, Size_30)
            , (Size_30, Size_1K)
            , (Size_3K, Size_3K)
            ]
        ]
      , -- 5. Structure variation tests (same total entries, different layouts)
        [ generateStructureTest g numPolicies tokensPerPolicy Size_30 Size_30
        | (numPolicies, tokensPerPolicy) <-
            [ (Size_1K, Size_1) -- 1000 policies x 1 token
            , (Size_100, Size_10) -- 100 policies x 10 tokens
            , (Size_10, Size_100) -- 10 policies x 100 tokens
            , (Size_1, Size_1K) -- 1 policy x 1000 tokens
            ]
        ]
      ]

-- | Generate lookup test with specified parameters
generateLookupTest
  :: (StatefulGen g m)
  => g
  -> Size -- Policy ID byte size
  -> Size -- Token name byte size
  -> Size -- Number of policies
  -> Size -- Tokens per policy
  -> m (ByteString, ByteString, Value)
generateLookupTest g pIdSize tNameSize numPolicies tokensPerPolicy = do
  value <- generateConstrainedValue numPolicies tokensPerPolicy pIdSize tNameSize g
  -- Generate lookup keys (may or may not exist in value)
  searchPolicyId <- generatePolicyId pIdSize g
  searchTokenName <- generateTokenName tNameSize g
  pure (searchPolicyId, searchTokenName, value)

-- | Generate budget-constrained test
generateBudgetTest
  :: (StatefulGen g m)
  => g
  -> Size -- Policy ID byte size
  -> Size -- Token name byte size
  -> Size -- Total budget
  -> m (ByteString, ByteString, Value)
generateBudgetTest g pIdSize tNameSize budget = do
  value <- generateValueWithBudget pIdSize tNameSize budget g
  searchPolicyId <- generatePolicyId pIdSize g
  searchTokenName <- generateTokenName tNameSize g
  pure (searchPolicyId, searchTokenName, value)

-- | Generate structure test
generateStructureTest
  :: (StatefulGen g m)
  => g
  -> Size -- Number of policies
  -> Size -- Tokens per policy
  -> Size -- Policy ID byte size
  -> Size -- Token name byte size
  -> m (ByteString, ByteString, Value)
generateStructureTest g numPolicies tokensPerPolicy pIdSize tNameSize = do
  value <- generateConstrainedValue numPolicies tokensPerPolicy pIdSize tNameSize g
  searchPolicyId <- generatePolicyId pIdSize g
  searchTokenName <- generateTokenName tNameSize g
  pure (searchPolicyId, searchTokenName, value)

valueContainsArgs :: StdGen -> [(Value, Value)]
valueContainsArgs gen = runStateGen_ gen $ \g -> do
  let
    keySizes = [Size_0, Size_30, Size_1K, Size_10K]
    valueSizes = [Size_1, Size_10, Size_100, Size_1K]

  sequence $
    concat
      [ -- Standard key tests with varying value sizes
        [ generateContainsTest g containerSize containedSize Size_30
        | containerSize <- valueSizes
        , containedSize <- valueSizes
        , sizeToInt containedSize <= sizeToInt containerSize
        ]
      , -- Key size impact tests
        [ generateContainsTest g Size_100 Size_10 keySize
        | keySize <- keySizes
        ]
      , -- Budget-constrained tests
        [ generateContainsBudgetTest g Size_30K keySize
        | keySize <- [Size_0, Size_30, Size_3K, Size_20K]
        ]
      , -- Edge cases
        [ generateEmptyContainedTest g containerSize Size_30
        | containerSize <- [Size_10, Size_100, Size_1K]
        ]
      ]

-- | Generate valueContains test with specified parameters
generateContainsTest
  :: (StatefulGen g m)
  => g
  -> Size -- Container value size
  -> Size -- Contained value size
  -> Size -- Key byte size (for both policy and token)
  -> m (Value, Value)
generateContainsTest g containerSize containedSize keySize = do
  -- Generate container value
  container <-
    generateConstrainedValue
      containerSize
      Size_10
      keySize
      keySize
      g

  -- Generate contained as subset of container (for true contains relationship)
  let containerList = Value.toList container
      containedEntries = take (sizeToInt containedSize) containerList

  let contained =
        Value.fromList $
          [ (pId, take (sizeToInt containedSize `div` max 1 (length containerList)) tokens)
          | (pId, tokens) <- containedEntries
          ]

  pure (container, contained)

-- | Generate budget-constrained contains test
generateContainsBudgetTest
  :: (StatefulGen g m)
  => g
  -> Size -- Total budget
  -> Size -- Key size
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
  -> Size -- Container size
  -> Size -- Key size
  -> m (Value, Value)
generateEmptyContainedTest g containerSize keySize = do
  container <- generateConstrainedValue containerSize Size_10 keySize keySize g
  pure (container, Value.empty)

--------------------------------------------------------------------------------
-- Generators for LookupCoin benchmarks ----------------------------------------

-- | Unified size type for comprehensive coverage within memory constraints
data Size
  = Size_0 -- 0 (empty strings, empty collections)
  | Size_1 -- 1
  | Size_10 -- 10
  | Size_30 -- 30 (standard 28-32 byte range)
  | Size_100 -- 100
  | Size_300 -- 300
  | Size_1K -- 1,000
  | Size_3K -- 3,000
  | Size_10K -- 10,000
  | Size_20K -- 20,000
  | Size_30K -- 30,000 (total memory budget)

-- | Convert size to exact integer value
sizeToInt :: Size -> Int
sizeToInt Size_0   = 0
sizeToInt Size_1   = 1
sizeToInt Size_10  = 10
sizeToInt Size_30  = 30
sizeToInt Size_100 = 100
sizeToInt Size_300 = 300
sizeToInt Size_1K  = 1_000
sizeToInt Size_3K  = 3_000
sizeToInt Size_10K = 10_000
sizeToInt Size_20K = 20_000
sizeToInt Size_30K = 30_000

-- | Generate ByteString of specified size
generateByteString :: (StatefulGen g m) => Size -> g -> m ByteString
generateByteString size g =
  let len = sizeToInt size
   in if len == 0
        then pure BS.empty
        else uniformByteStringM len g

-- | Generate policy ID of specified size
generatePolicyId :: (StatefulGen g m) => Size -> g -> m ByteString
generatePolicyId = generateByteString

-- | Generate token name of specified size
generateTokenName :: (StatefulGen g m) => Size -> g -> m ByteString
generateTokenName = generateByteString

-- | Generate constrained Value with total size budget
generateConstrainedValue
  :: (StatefulGen g m)
  => Size -- Number of policies
  -> Size -- Number of tokens per policy
  -> Size -- Policy ID byte length
  -> Size -- Token name byte length
  -> g
  -> m Value
generateConstrainedValue numPoliciesSize tokensPerPolicySize pIdSize tNameSize g = do
  policyIds <- -- Generate policy IDs of specified size
    replicateM (sizeToInt numPoliciesSize) (generatePolicyId pIdSize g)

  tokenNames <- -- Generate token names of specified size
    replicateM (sizeToInt tokensPerPolicySize) (generateTokenName tNameSize g)

  -- Generate positive quantities (1 to 1000000)
  let quantity :: Int -> Int -> Integer
      quantity policyIdx tokenIdx =
        fromIntegral (1 + (policyIdx * 1_000 + tokenIdx) `mod` 1_000_000)

      nestedMap :: [(ByteString, [(ByteString, Integer)])]
      nestedMap =
        [ ( policyId
          , [ (tokenName, quantity policyIdx tokenIdx)
            | (tokenIdx, tokenName) <- zip [0 ..] tokenNames
            ]
          )
        | (policyIdx, policyId) <- zip [0 ..] policyIds
        ]
  pure $ Value.fromList nestedMap

-- | Generate Value within total size budget
generateValueWithBudget
  :: (StatefulGen g m)
  => Size -- Policy ID byte length
  -> Size -- Token name byte length
  -> Size -- Target total size budget
  -> g
  -> m Value
generateValueWithBudget pIdSize tNameSize totalBudget g = do
  let
    pIdBytes = sizeToInt pIdSize
    tNameBytes = sizeToInt tNameSize
    budget = sizeToInt totalBudget
    overhead = 8 -- bytes per amount

    -- Calculate maximum possible entries
    bytesPerEntry = pIdBytes + tNameBytes + overhead
    maxEntries =
      if bytesPerEntry > 0
        then min (budget `div` bytesPerEntry) budget
        else budget -- Handle Size_0 case

    -- Simple distribution: try to balance policies and tokens
    numPolicies = max 1 (floor (sqrt (fromIntegral maxEntries :: Double)))
    tokensPerPolicy = if numPolicies > 0 then maxEntries `div` numPolicies else 0

  generateConstrainedValue
    (intToSize numPolicies)
    (intToSize tokensPerPolicy)
    pIdSize
    tNameSize
    g

-- | Convert integer back to nearest Size (helper function)
intToSize :: Int -> Size
intToSize n
  | n <= 0 = Size_0
  | n <= 1 = Size_1
  | n <= 10 = Size_10
  | n <= 30 = Size_30
  | n <= 100 = Size_100
  | n <= 300 = Size_300
  | n <= 1000 = Size_1K
  | n <= 3000 = Size_3K
  | n <= 10_000 = Size_10K
  | n <= 20_000 = Size_20K
  | otherwise = Size_30K
