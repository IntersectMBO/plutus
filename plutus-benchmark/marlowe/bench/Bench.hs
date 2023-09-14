{-# LANGUAGE RecordWildCards #-}

{- | Plutus benchmarks based on some Marlowe examples. -}

module Main where
import Criterion.Main (Benchmark, Benchmarkable, bench, bgroup, defaultMainWith)

import PlutusBenchmark.Common (benchProgramCek, getConfig)
import PlutusBenchmark.Marlowe.BenchUtil (benchmarkToUPLC, rolePayoutBenchmarks,
                                          semanticsBenchmarks)
import PlutusBenchmark.Marlowe.Scripts.RolePayout (rolePayoutValidator)
import PlutusBenchmark.Marlowe.Scripts.Semantics (marloweValidator)
import PlutusBenchmark.Marlowe.Types qualified as M
import PlutusLedgerApi.V2 (scriptContextTxInfo, txInfoId)
import PlutusTx.Code (CompiledCode)

mkBenchmarkable :: CompiledCode a -> M.Benchmark -> (String, Benchmarkable)
mkBenchmarkable validator bm@M.Benchmark{..} =
  let benchName = show $ txInfoId $ scriptContextTxInfo bScriptContext
  in
    (benchName, benchProgramCek $ benchmarkToUPLC validator bm )

main :: IO ()
main = do

  -- Read the semantics benchmark files.
  semanticsMBench <- either error id <$> semanticsBenchmarks

  -- Read the role payout benchmark files.
  rolePayoutMBench <- either error id <$> rolePayoutBenchmarks

  let
    uncurriedBench :: (String, Benchmarkable) -> Benchmark
    uncurriedBench = uncurry bench
    semanticsBench :: [Benchmark] -- list of criterion semantics Benchmarks
    semanticsBench =
      fmap (uncurriedBench . mkBenchmarkable marloweValidator) semanticsMBench
    rolePayoutBench :: [Benchmark] -- list of criterion role payout Benchmarks
    rolePayoutBench =
      fmap (uncurriedBench . mkBenchmarkable rolePayoutValidator) rolePayoutMBench

  -- Run each benchmark for 5 secs by default. This benchmark runs on the longitudinal
  -- benchmarking flow so we don't want to set it higher by default. One can change this with -L or
  -- --timeout when running locally.
  config <- getConfig 5.0
  defaultMainWith config [
    bgroup "semantics" semanticsBench
    , bgroup "role-payout" rolePayoutBench]
