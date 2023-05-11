
{-# LANGUAGE ImportQualifiedPost #-}


module Benchmark.Marlowe.Types (
  Benchmark(..)
, makeBenchmark
) where


import PlutusLedgerApi.V2 qualified as V2


data Benchmark =
  Benchmark
  {
    bDatum         :: V2.Data
  , bRedeemer      :: V2.Data
  , bScriptContext :: V2.ScriptContext
  , bReferenceCost :: Maybe V2.ExBudget
  }
    deriving Show


makeBenchmark
  :: V2.ToData d
  => V2.ToData r
  => d
  -> r
  -> V2.ScriptContext
  -> Maybe V2.ExBudget
  -> Benchmark
makeBenchmark datum redeemer = Benchmark (V2.toData datum) (V2.toData redeemer)
