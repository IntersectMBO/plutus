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

{-| Build one Criterion benchmark per fixture file.

The benchmark name is the transaction id stored inside the fixture, so we read
every file once up front just to learn its name, forcing the name and dropping
everything else.  The fixture itself is then reloaded inside Criterion's `env`
only when (and if) that benchmark is selected, and a major GC is performed after
loading.  This keeps the rest of the corpus out of the live heap while a
benchmark is being measured; a large retained heap makes the cost of major
collections inside the timed region highly variable (see
https://github.com/IntersectMBO/plutus/issues/8024). -}
mkBenchmarks
  :: (Program -> Benchmarkable)
  -> Program
  -> FilePath
  -> IO [Benchmark]
mkBenchmarks benchmarker validator subfolder = do
  dir <- getDataDir
  let folder = dir </> subfolder
  files <- sort . filter (isSuffixOf ".benchmark") <$> listDirectory folder
  forM files $ \file -> do
    let path = folder </> file
    name <- benchName <$> load path
    _ <- evaluate (force name)
    pure $
      env (loadProgram path) $ \ ~prog ->
        bench name (benchmarker prog)
  where
    load path = either error rescript <$> readBenchmark path
    benchName M.Benchmark {..} = show $ txInfoId $ scriptContextTxInfo bScriptContext
    loadProgram path = do
      prog <- evaluate . force . benchmarkToUPLC validator =<< load path
      performMajorGC
      pure prog

runBenchmarks :: (Program -> Benchmarkable) -> IO ()
runBenchmarks benchmarker = do
  dir <- getDataDir

  marloweValidator <- readFlat $ dir </> "marlowe/scripts/semantics/validator/sop.flat"
  rolePayoutValidator <- readFlat $ dir </> "marlowe/scripts/rolepayout/validator/sop.flat"

  semanticsBench <- mkBenchmarks benchmarker marloweValidator "marlowe/scripts/semantics"
  rolePayoutBench <- mkBenchmarks benchmarker rolePayoutValidator "marlowe/scripts/rolepayout"

  -- Run each benchmark for 5 secs by default. This benchmark runs on the
  -- longitudinal benchmarking flow so we don't want to set it higher by
  -- default. One can change this with -L or --timeout when running locally.
  config <- getConfig 5.0
  defaultMainWith
    config
    [ bgroup "semantics" semanticsBench
    , bgroup "role-payout" rolePayoutBench
    ]
