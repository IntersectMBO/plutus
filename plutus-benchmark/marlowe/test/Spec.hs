{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Foldable (for_)
import Data.List qualified as List
import Lib qualified
import Main.Utf8 (withUtf8)
import PlutusBenchmark.Common (checkGoldenFileExists)
import PlutusBenchmark.Marlowe.BenchUtil (readAppliedValidators)
import PlutusLedgerApi.V3 (ExCPU (..), ExMemory (..))
import System.FilePath ((</>))
import System.IO (hPutStrLn)
import Test.Tasty (defaultMain, testGroup)
import UntypedPlutusCore.AstSize (AstSize (..))

-- Reads validator scripts and its benchmark cases, runs and measures it for
-- each of the cases
measure :: FilePath -> FilePath -> IO [(ExCPU, ExMemory, AstSize)]
measure validatorPath argsPath = do
  programs <- readAppliedValidators validatorPath argsPath
  mapM Lib.measureProgram programs

main :: IO ()
main = withUtf8 $ do
  let dir = "marlowe" </> "test"
      goldenFile = dir </> "budgets.golden.tsv"
      goldenFileData = dir </> "data.budgets.golden.tsv"
      actualFile = dir </> "budgets.actual.tsv"
      actualFileData = dir </> "data.budgets.actual.tsv"
  checkGoldenFileExists goldenFile -- See Note [Paths to golden files]
  semanticsMeasures <- measure "marlowe/scripts/semantics/validator.flat" "marlowe/scripts/semantics"
  -- dataSemanticsMeasures <- measure "marlowe/scripts/semantics-data/validator.flat" "marlowe/scripts/semantics"
  rolePayoutMeasures <- measure "marlowe/scripts/rolepayout/validator.flat" "marlowe/scripts/semantics"
  -- dataRolePayoutMeasures <- measure "marlowe/scripts/rolepayout-data/validator.flat" "marlowe/scripts/semantics"

  -- Write the measures to the actual file
  defaultMain $
    testGroup
      "Marlowe"
      [ Lib.goldenUplcMeasurements "budgets" goldenFile actualFile \writeHandle ->
          for_
            (semanticsMeasures <> rolePayoutMeasures)
            \(ExCPU cpu, ExMemory mem, AstSize size) ->
              hPutStrLn writeHandle $
                List.intercalate "\t" [show cpu, show mem, show size]
                --      , Lib.goldenUplcMeasurements "data-budgets" goldenFileData actualFileData \writeHandle ->
                --          for_
                --            (dataSemanticsMeasures <> dataRolePayoutMeasures)
                --            \(ExCPU cpu, ExMemory mem, AstSize size) ->
                --              hPutStrLn writeHandle $
                --                List.intercalate "\t" [show cpu, show mem, show size]
      ]
