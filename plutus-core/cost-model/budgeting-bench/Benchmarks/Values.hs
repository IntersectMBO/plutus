module Benchmarks.Values (
    makeBenchmarks,
) where

import Prelude

import Common

import PlutusCore (DefaultFun (InsertCoin, LookupCoin, UnValueData, ValueContains, ValueData))
import PlutusCore.Value (Value)
import PlutusCore.Value qualified as Value

import Control.Monad.State (State)
import Criterion.Main (Benchmark)
import Data.ByteString (ByteString)
import System.Random.Stateful (StageGenM, StatefulGen, StdGen, UniformRange (uniformRM),
                               runStateGen_, uniformByteStringM)

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen =
    [ benchInsertCoin gen
    -- , benchUnionValue gen
    ]

type PolicyId = ByteString
type TokenName = ByteString
type Amount = Integer

-- | An insertCoin benchmark is a concrete set of arguments we apply to the
-- InsertCoin builtin function to measure its runtime cost.
data InsertCoinBenchmark = InsertCoinBenchmark
    { icPolicyId  :: PolicyId
    , icTokenName :: TokenName
    , icAmount    :: Amount
    , icValue     :: Value
    }

icToTuple :: InsertCoinBenchmark -> (PolicyId, TokenName, Amount, Value)
icToTuple (InsertCoinBenchmark p t a v) = (p, t, a, v)

benchInsertCoin :: StdGen -> Benchmark
benchInsertCoin gen =
    createFourTermBuiltinBenchElementwiseWithWrappers
        (id, id, id, id) -- TODO: use proper wrappers
        InsertCoin
        []
        (icToTuple <$> insertCoinBenchGen gen)

-- | Generate a set of benchmarks for the InsertCoin builtin function.
-- It includes the following scenarios:
--   1. Inserting into an empty Value.
--   2. Inserting a new TokenName into an existing PolicyId.
--   3. Inserting into an existing TokenName.
--   4. Inserting a new PolicyId.
--   5. Deleting a TokenName by inserting a 0 amount.
--   6. Deleting a PolicyId by inserting a 0 amount into its last TokenName.
-- We're interested in the worst case performance, so we'll use the largest key values possible.
insertCoinBenchGen
    :: StdGen
    -> [InsertCoinBenchmark]
insertCoinBenchGen g = undefined

uniformByteString :: StdGen -> ByteString
uniformByteString gen = uniformByteString Value.maxKeyLen gen
