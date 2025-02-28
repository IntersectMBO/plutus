{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Foldable (for_)
import Data.List qualified as List
import Lib qualified
import Main.Utf8 (withUtf8)
import PlutusBenchmark.Common (checkGoldenFileExists)
import PlutusBenchmark.Marlowe.BenchUtil (benchmarkToUPLC, rolePayoutBenchmarks,
                                          semanticsBenchmarks)
import PlutusBenchmark.Marlowe.Scripts.RolePayout (rolePayoutValidator)
import PlutusBenchmark.Marlowe.Scripts.Semantics (marloweValidator)
import PlutusLedgerApi.V3 (ExCPU (..), ExMemory (..))
import System.FilePath ((</>))
import System.IO (hPutStrLn)
import Test.Tasty (defaultMain)
import UntypedPlutusCore.Size qualified as UPLC

main :: IO ()
main = withUtf8 do
  let dir = "marlowe" </> "test"
      goldenFile = dir </> "budgets.golden.tsv"
      actualFile = dir </> "budgets.actual.tsv"
  checkGoldenFileExists goldenFile -- See Note [Paths to golden files]

  -- Measure ExCPU, ExMemory, and UPLC.Size for each "semantics" benchmark
  semanticsMeasures <-
    semanticsBenchmarks >>= \case
      Left err -> fail $ "Error generating semantics benchmarks: " <> show err
      Right semantics ->
        traverse
          Lib.measureProgram
          [benchmarkToUPLC marloweValidator bench | bench <- semantics]

  -- Measure ExCPU, ExMemory, and UPLC.Size for each "role payout" benchmark
  rolePayoutMeasures <-
    rolePayoutBenchmarks >>= \case
      Left err -> fail $ "Error generating role payout benchmarks: " <> show err
      Right rolePayout ->
        traverse
          Lib.measureProgram
          [benchmarkToUPLC rolePayoutValidator bench | bench <- rolePayout]

  -- Write the measures to the actual file
  defaultMain do
    Lib.goldenUplcMeasurements "budgets" goldenFile actualFile \writeHandle ->
      for_
        (semanticsMeasures <> rolePayoutMeasures)
        \(ExCPU cpu, ExMemory mem, UPLC.Size size) ->
          hPutStrLn writeHandle $
            List.intercalate "\t" [show cpu, show mem, show size]
