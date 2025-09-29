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
lookupCoinArgs gen = runStateGen_ gen \g -> do
  let testValues = generateTestValues gen

  -- Add random search keys to each test value
  sequence
    [ (,,value) <$> generatePolicyId g <*> generateTokenName g
    | value <- testValues
    ]

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
valueContainsArgs gen = runStateGen_ gen \g ->
  sequence $
    -- Use test values as containers with empty contained value (edge case)
    [pure (container, Value.empty) | container <- generateTestValues gen]
      ++
      -- Random contains tests with varied entry counts
      replicate 100 do
        containerEntries <- uniformRM (1, 1000) g
        containedEntries <- uniformRM (0, containerEntries) g

        -- Generate container
        container <- generateRandomValueForContains containerEntries g

        -- Generate contained as subset
        let containerList = Value.toList container
            containedList = take containedEntries containerList
            contained = Value.fromList containedList

        pure (container, contained)

-- | Generate Value for contains tests with exact entry count
generateRandomValueForContains
  :: (StatefulGen g m)
  => Int -- Entry count
  -> g
  -> m Value
generateRandomValueForContains entryCount g = do
  -- Generate policies and tokens with exact entry count (realistic sizes)
  policyIds <- replicateM entryCount (generatePolicyId g)
  tokenNames <- replicateM entryCount (generateTokenName g)

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
valueDataBenchmark gen =
  createOneTermBuiltinBenchWithWrapper ValueTotalSize ValueData [] (generateTestValues gen)

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
  sequence $
    -- Specific cases of interest
    [ generateConstrainedValue 1 2000 g -- 1 policy with 2000 tokens
    , generateConstrainedValue 2000 1 g -- 2000 policies with 1 token each
    , pure Value.empty -- Empty value as edge case
    ]
      ++
      -- Random test values (~100 combinations)
      replicate
        100
        ( do
            numPolicies <- uniformRM (0, 2000) g -- 0-2000 policies
            let maxTokens = if numPolicies == 0 then 2000 else 10_000 `div` numPolicies
            tokensPerPolicy <- uniformRM (1, min 2000 maxTokens) g -- Cap at 10,000 total entries
            generateConstrainedValue numPolicies tokensPerPolicy g
        )

-- | Generate constrained Value
generateConstrainedValue
  :: (StatefulGen g m)
  => Int -- Number of policies
  -> Int -- Number of tokens per policy
  -> g
  -> m Value
generateConstrainedValue numPolicies tokensPerPolicy g = do
  -- Handle edge case: no policies means empty value
  if numPolicies <= 0
    then pure Value.empty
    else do
      policyIds <- -- Generate policy IDs (always 28 bytes)
        replicateM numPolicies (generatePolicyId g)

      tokenNames <- -- Generate token names (random 0-32 bytes)
        replicateM tokensPerPolicy (generateTokenName g)

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

----------------------------------------------------------------------------------------------------
-- Other Generators --------------------------------------------------------------------------------

-- | Generate policy ID of exactly 28 bytes (MintingPolicyHash size)
generatePolicyId :: (StatefulGen g m) => g -> m ByteString
generatePolicyId = uniformByteStringM 28

-- | Generate token name of random size (0-32 bytes)
generateTokenName :: (StatefulGen g m) => g -> m ByteString
generateTokenName g = do
  tokenSize <- uniformRM (0, 32) g
  uniformByteStringM tokenSize g
