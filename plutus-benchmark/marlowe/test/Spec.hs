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
import PlutusBenchmark.Marlowe.Scripts.Data.RolePayout qualified as Data (rolePayoutValidator)
import PlutusBenchmark.Marlowe.Scripts.Data.Semantics qualified as Data (marloweValidator)
import PlutusBenchmark.Marlowe.Scripts.RolePayout qualified as SOP (rolePayoutValidator)
import PlutusBenchmark.Marlowe.Scripts.Semantics qualified as SOP (marloweValidator)
import PlutusLedgerApi.V3 (ExCPU (..), ExMemory (..))
import System.FilePath ((</>))
import System.IO (hPutStrLn)
import Test.Tasty (defaultMain, testGroup)
import UntypedPlutusCore.AstSize qualified as UPLC

main :: IO ()
main = withUtf8 $ do

  let dir = "marlowe" </> "test"
      goldenFile = dir </> "budgets.golden.tsv"
      goldenFileData = dir </> "data.budgets.golden.tsv"
      actualFile = dir </> "budgets.actual.tsv"
      actualFileData = dir </> "data.budgets.actual.tsv"
  checkGoldenFileExists goldenFile -- See Note [Paths to golden files]

  -- Measure ExCPU, ExMemory, and UPLC.AstSize for each "semantics" benchmark
  semanticsMeasures <-
    semanticsBenchmarks >>= \case
      Left err -> fail $ "Error generating semantics benchmarks: " <> show err
      Right semantics ->
        traverse
          Lib.measureProgram
          [benchmarkToUPLC SOP.marloweValidator bench | bench <- semantics]

  dataSemanticsMeasures <-
    semanticsBenchmarks >>= \case
      Left err -> fail $ "Error generating semantics benchmarks: " <> show err
      Right semantics ->
        traverse
          Lib.measureProgram
          [benchmarkToUPLC Data.marloweValidator bench | bench <- semantics]

  -- Measure ExCPU, ExMemory, and UPLC.AstSize for each "role payout" benchmark
  rolePayoutMeasures <-
    rolePayoutBenchmarks >>= \case
      Left err -> fail $ "Error generating role payout benchmarks: " <> show err
      Right rolePayout ->
        traverse
          Lib.measureProgram
          [benchmarkToUPLC SOP.rolePayoutValidator bench | bench <- rolePayout]

  dataRolePayoutMeasures <-
    rolePayoutBenchmarks >>= \case
      Left err -> fail $ "Error generating role payout benchmarks: " <> show err
      Right rolePayout ->
        traverse
          Lib.measureProgram
          [benchmarkToUPLC Data.rolePayoutValidator bench | bench <- rolePayout]

  -- Write the measures to the actual file
  defaultMain
    $ testGroup "Marlowe"
    [ Lib.goldenUplcMeasurements "budgets" goldenFile actualFile \writeHandle ->
        for_
          (semanticsMeasures <> rolePayoutMeasures)
          \(ExCPU cpu, ExMemory mem, UPLC.AstSize size) ->
            hPutStrLn writeHandle $
              List.intercalate "\t" [show cpu, show mem, show size]
    , Lib.goldenUplcMeasurements "data-budgets" goldenFileData actualFileData \writeHandle ->
        for_
          (dataSemanticsMeasures <> dataRolePayoutMeasures)
          \(ExCPU cpu, ExMemory mem, UPLC.AstSize size) ->
            hPutStrLn writeHandle $
              List.intercalate "\t" [show cpu, show mem, show size]
    ]
