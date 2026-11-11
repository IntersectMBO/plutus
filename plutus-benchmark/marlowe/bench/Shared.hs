-- | Plutus benchmarks based on some Marlowe examples.
module Shared where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (forM)
import Criterion.Main (Benchmark, Benchmarkable, bench, bgroup, defaultMainWith, env)
import Data.List (isSuffixOf, sort)
import System.Directory (listDirectory)
import System.Mem (performMajorGC)

import PlutusBenchmark.Common (Program, getConfig, getDataDir)
import PlutusBenchmark.Marlowe.BenchUtil
  ( benchmarkToUPLC
  , readBenchmark
  , readFlat
  , rescript
  )
import PlutusBenchmark.Marlowe.Types qualified as M
import PlutusLedgerApi.V2 (scriptContextTxInfo, txInfoId)
import System.FilePath

-- | One benchmark per fixture. Each fixture is loaded only when its benchmark
-- runs, so the rest of the corpus isn't in the heap during measurement (#8024).
mkBenchmarks :: (Program -> Benchmarkable) -> Program -> FilePath -> IO [Benchmark]
mkBenchmarks benchmarker validator folder = do
  files <- map (folder </>) . sort . filter (isSuffixOf ".benchmark") <$> listDirectory folder
  forM files $ \file -> do
    name <- evaluate . force . benchName =<< load file
    pure $ env (prepare file) $ \ ~prog -> bench name (benchmarker prog)
  where
    load file = either error rescript <$> readBenchmark file
    benchName = show . txInfoId . scriptContextTxInfo . M.bScriptContext
    prepare file = (evaluate . force . benchmarkToUPLC validator =<< load file) <* performMajorGC

runBenchmarks :: (Program -> Benchmarkable) -> IO ()
runBenchmarks benchmarker = do
  dir <- getDataDir

  let group name = do
        let folder = dir </> "marlowe/scripts" </> name
        validator <- readFlat $ folder </> "validator/sop.flat"
        mkBenchmarks benchmarker validator folder
  semanticsBench <- group "semantics"
  rolePayoutBench <- group "rolepayout"

  -- Run each benchmark for 5 secs by default. This benchmark runs on the
  -- longitudinal benchmarking flow so we don't want to set it higher by
  -- default. One can change this with -L or --timeout when running locally.
  config <- getConfig 5.0
  defaultMainWith
    config
    [ bgroup "semantics" semanticsBench
    , bgroup "role-payout" rolePayoutBench
    ]
