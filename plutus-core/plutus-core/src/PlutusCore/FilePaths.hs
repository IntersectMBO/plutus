-- | Various file paths used in plutus-core, mostly related to the cost model.

module PlutusCore.FilePaths
where

import           System.FilePath

costModelDataDir :: FilePath
costModelDataDir = "cost-model" </> "data"

modelFile :: FilePath
modelFile = costModelDataDir </> "models" <.> "R"

benchingResultsFile :: FilePath
benchingResultsFile = costModelDataDir </> "benching" <.> "csv"

backupBenchingResultsFile :: FilePath
backupBenchingResultsFile = benchingResultsFile <.> "backup"

builtinCostModelFile :: FilePath
builtinCostModelFile = costModelDataDir </> "builtinCostModel" <.> "json"

cekMachineCostsFile :: FilePath
cekMachineCostsFile = costModelDataDir </> "cekMachineCosts" <.> "json"
