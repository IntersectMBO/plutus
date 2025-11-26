-- | Types for benchmarking Marlowe validators.
module PlutusBenchmark.Marlowe.Types
  ( Benchmark (..)
  , makeBenchmark
  ) where

import PlutusLedgerApi.V2 (Data, ExBudget, ScriptContext, ToData, toData)

-- | A benchmarking case.
data Benchmark = Benchmark
  { bDatum :: Data
  -- ^ The datum.
  , bRedeemer :: Data
  -- ^ The redeemer.
  , bScriptContext :: ScriptContext
  -- ^ The script context.
  , bReferenceCost :: Maybe ExBudget
  {-^ The previously measured execution costs in production,
  which uses the Plutus version on August 18 2022
  (commit 6ed578b592f46afc0e77f4d19e5955a6eb439ba4). -}
  }
  deriving stock (Show)

-- | Construct a benchmarking case.
makeBenchmark
  :: (ToData d, ToData r)
  => d
  -> r
  -> ScriptContext
  -> Maybe ExBudget
  -> Benchmark
makeBenchmark datum redeemer = Benchmark (toData datum) (toData redeemer)
