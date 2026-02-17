{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Foldable (for_)
import Data.List qualified as List
import Lib qualified
import Main.Utf8 (withUtf8)
import PlutusBenchmark.Common (checkGoldenFileExists)
import PlutusBenchmark.Marlowe.BenchUtil
import PlutusLedgerApi.V3 (ExCPU (..), ExMemory (..))
import System.FilePath ((</>))
import System.IO (hPutStrLn)
import Test.Tasty (defaultMain, testGroup)
import UntypedPlutusCore.AstSize (AstSize (..))

main :: IO ()
main = withUtf8 $ do
  let dir = "marlowe" </> "test"
      scriptDir = "marlowe" </> "scripts"
      goldenFile = dir </> "budgets.golden.tsv"
      goldenFileData = dir </> "data.budgets.golden.tsv"
      actualFile = dir </> "budgets.actual.tsv"
      actualFileData = dir </> "data.budgets.actual.tsv"
  checkGoldenFileExists goldenFile -- See Note [Paths to golden files]
  let
    benchSOP =
      [ (scriptDir </> "semantics/validator.flat", semanticsBenchmarks)
      , (scriptDir </> "rolepayout/validator.flat", rolePayoutBenchmarks)
      ]
    benchData =
      [ (scriptDir </> "semantics/validator-data.flat", semanticsBenchmarks)
      , (scriptDir </> "rolepayout/validator-data.flat", rolePayoutBenchmarks)
      ]

    measure (validatorPath, getCases) = do
      validator <- readFlat validatorPath
      getCases >>= \case
        Left err -> fail $ "Error generating benchmarks: " <> show err
        Right cases ->
          traverse
            Lib.measureProgram
            [benchmarkToUPLC validator bench | bench <- cases]

  measuresSOP <- mapM measure benchSOP
  measuresData <- mapM measure benchData

  -- Write the measures to the actual file
  defaultMain $
    testGroup
      "Marlowe"
      [ Lib.goldenUplcMeasurements "budgets" goldenFile actualFile \writeHandle ->
          for_
            (mconcat measuresSOP)
            \(ExCPU cpu, ExMemory mem, AstSize size) ->
              hPutStrLn writeHandle $
                List.intercalate "\t" [show cpu, show mem, show size]
      , Lib.goldenUplcMeasurements "data-budgets" goldenFileData actualFileData \writeHandle ->
          for_
            (mconcat measuresData)
            \(ExCPU cpu, ExMemory mem, AstSize size) ->
              hPutStrLn writeHandle $
                List.intercalate "\t" [show cpu, show mem, show size]
      ]
