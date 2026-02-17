-- | Plutus benchmarks based on some Marlowe examples.
module Shared where

import Criterion.Main (Benchmark, Benchmarkable, bench, bgroup, defaultMainWith)

import PlutusBenchmark.Common (Program, getConfig, getDataDir)
import PlutusBenchmark.Marlowe.BenchUtil
  ( benchmarkToUPLC
  , readFlat
  , rolePayoutBenchmarks
  , semanticsBenchmarks
  )
import PlutusBenchmark.Marlowe.Types qualified as M
import PlutusLedgerApi.V2 (scriptContextTxInfo, txInfoId)
import PlutusTx.Code (CompiledCode)
import System.FilePath

mkBenchmarkable
  :: (Program -> Benchmarkable)
  -> Program
  -> M.Benchmark
  -> (String, Benchmarkable)
mkBenchmarkable benchmarker validator bm@M.Benchmark {..} =
  let benchName = show $ txInfoId $ scriptContextTxInfo bScriptContext
   in (benchName, benchmarker $ benchmarkToUPLC validator bm)

runBenchmarks :: (Program -> Benchmarkable) -> IO ()
runBenchmarks benchmarker = do
  dir <- getDataDir

  -- Read the semantics benchmark files.
  marloweValidator <- readFlat $ dir </> "marlowe/scripts/semantics/validator.flat"
  semanticsMBench <- either error id <$> semanticsBenchmarks

  -- Read the role payout benchmark files.
  rolePayoutValidator <- readFlat $ dir </> "marlowe/scripts/rolepayout/validator.flat"
  rolePayoutMBench <- either error id <$> rolePayoutBenchmarks

  let
    uncurriedBench :: (String, Benchmarkable) -> Benchmark
    uncurriedBench = uncurry bench

    semanticsBench :: [Benchmark] -- list of criterion semantics Benchmarks
    semanticsBench =
      fmap (uncurriedBench . mkBenchmarkable benchmarker marloweValidator) semanticsMBench
    rolePayoutBench :: [Benchmark] -- list of criterion role payout Benchmarks
    rolePayoutBench =
      fmap (uncurriedBench . mkBenchmarkable benchmarker rolePayoutValidator) rolePayoutMBench

  -- Run each benchmark for 5 secs by default. This benchmark runs on the
  -- longitudinal benchmarking flow so we don't want to set it higher by
  -- default. One can change this with -L or --timeout when running locally.
  config <- getConfig 5.0
  defaultMainWith
    config
    [ bgroup "semantics" semanticsBench
    , bgroup "role-payout" rolePayoutBench
    ]
