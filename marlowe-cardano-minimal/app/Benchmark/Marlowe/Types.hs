

-----------------------------------------------------------------------------
--
-- Module      :  $Headers
-- License     :  Apache 2.0
--
-- Stability   :  Experimental
-- Portability :  Portable
--
-- | Types for benchmarking Marlowe validators.
--
-----------------------------------------------------------------------------


module Benchmark.Marlowe.Types (
  -- * Benchmarking
  Benchmark(..)
, makeBenchmark
) where


import PlutusLedgerApi.V2 (Data, ExBudget, ScriptContext, ToData, toData)


-- | A benchmarking case.
data Benchmark =
  Benchmark
  {
    bDatum         :: Data  -- ^ The datum.
  , bRedeemer      :: Data  -- ^ The redeemer.
  , bScriptContext :: ScriptContext  -- ^ The script context.
  , bReferenceCost :: Maybe ExBudget  -- ^ The previously measured execution costs.
  }
    deriving Show


-- | Construct a benchmarking case.
makeBenchmark
  :: ToData d
  => ToData r
  => d
  -> r
  -> ScriptContext
  -> Maybe ExBudget
  -> Benchmark
makeBenchmark datum redeemer = Benchmark (toData datum) (toData redeemer)
