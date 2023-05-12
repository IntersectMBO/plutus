
module Benchmark.Marlowe.Types (
  Benchmark(..)
, makeBenchmark
) where


import PlutusLedgerApi.V2 (Data, ExBudget, ScriptContext, ToData, toData)


data Benchmark =
  Benchmark
  {
    bDatum         :: Data
  , bRedeemer      :: Data
  , bScriptContext :: ScriptContext
  , bReferenceCost :: Maybe ExBudget
  }
    deriving Show


makeBenchmark
  :: ToData d
  => ToData r
  => d
  -> r
  -> ScriptContext
  -> Maybe ExBudget
  -> Benchmark
makeBenchmark datum redeemer = Benchmark (toData datum) (toData redeemer)
