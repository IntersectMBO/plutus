-- | Various file paths used in plutus-core, currently all to do with the cost
-- model.

module PlutusCore.DataFilePaths
where

import System.FilePath

costModelDataDir :: FilePath
costModelDataDir = "cost-model" </> "data"

builtinCostModelFile :: FilePath
builtinCostModelFile = costModelDataDir </> "builtinCostModel" <.> "json"

cekMachineCostsFile :: FilePath
cekMachineCostsFile = costModelDataDir </> "cekMachineCosts" <.> "json"

-- | The file containing the R models: only needed for cost-model-test.
rModelFile :: FilePath
rModelFile = costModelDataDir </> "models" <.> "R"

-- | The file containing the benchmark results for the built-in functions: only
-- needed for cost-model-test.
benchingResultsFile :: FilePath
benchingResultsFile = costModelDataDir </> "benching" <.> "csv"

