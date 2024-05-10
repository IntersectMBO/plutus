-- | Various file paths used in plutus-core, currently all to do with the cost
-- model.

module PlutusCore.DataFilePaths
where

import System.FilePath

costModelDataDir :: FilePath
costModelDataDir = "cost-model" </> "data"

builtinCostModelFileA :: FilePath
builtinCostModelFileA = costModelDataDir </> "builtinCostModelA" <.> "json"

cekMachineCostsFileA :: FilePath
cekMachineCostsFileA = costModelDataDir </> "cekMachineCostsA" <.> "json"

builtinCostModelFileB :: FilePath
builtinCostModelFileB = costModelDataDir </> "builtinCostModelB" <.> "json"

cekMachineCostsFileB :: FilePath
cekMachineCostsFileB = costModelDataDir </> "cekMachineCostsB" <.> "json"

builtinCostModelFileC :: FilePath
builtinCostModelFileC = costModelDataDir </> "builtinCostModelC" <.> "json"

cekMachineCostsFileC :: FilePath
cekMachineCostsFileC = costModelDataDir </> "cekMachineCostsC" <.> "json"

-- | The file containing the R models: only needed for cost-model-test.
rModelFile :: FilePath
rModelFile = costModelDataDir </> "models" <.> "R"

-- | The file containing the benchmark results for the built-in functions: only
-- needed for cost-model-test.
benchingResultsFile :: FilePath
benchingResultsFile = costModelDataDir </> "benching" <.> "csv"

