-- | Various file paths used in plutus-core, currently all to do with the cost
-- model.

-- Note that a couple of these paths are also used inside an inline-r splice in
-- CostModelCreation.hs but we have to use literal strings there, not the
-- versions defined here.  Those strings will also have to be updated if things
-- change here.

module PlutusCore.DataFilePaths
where

import System.FilePath

costModelDataDir :: FilePath
costModelDataDir = "cost-model" </> "data"

builtinCostModelFile :: FilePath
builtinCostModelFile = costModelDataDir </> "builtinCostModel" <.> "json"

cekMachineCostsFile :: FilePath
cekMachineCostsFile = costModelDataDir </> "cekMachineCosts" <.> "json"

-- | The file containing the R models: only needed for cost-model-test
rModelFile :: FilePath
rModelFile = costModelDataDir </> "models" <.> "R"

-- | The file containig the benchmark results for the built-in functions:
-- only needed for cost-model-test
benchingResultsFile :: FilePath
benchingResultsFile = costModelDataDir </> "benching" <.> "csv"

