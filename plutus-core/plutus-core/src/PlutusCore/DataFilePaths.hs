-- | Various file paths used in plutus-core, currently all to do with the cost
-- model.

-- Note that a couple of these paths are also used inside an inline-r splice in
-- CostModelCreation.hs but we have to use literal strings there, not the
-- versions defined here.  Those strings will also have to be updated if things
-- change here.

module PlutusCore.DataFilePaths
where

import           System.FilePath

costModelDataDir :: FilePath
costModelDataDir = "cost-model" </> "data"

-- A literal version of this is also used in CostModelCreation.hs
modelFile :: FilePath
modelFile = costModelDataDir </> "models" <.> "R"

-- A literal version of this is also used in CostModelCreation.hs
benchingResultsFile :: FilePath
benchingResultsFile = costModelDataDir </> "benching" <.> "csv"

backupBenchingResultsFile :: FilePath
backupBenchingResultsFile = benchingResultsFile <.> "backup"

builtinCostModelFile :: FilePath
builtinCostModelFile = costModelDataDir </> "builtinCostModel" <.> "json"

cekMachineCostsFile :: FilePath
cekMachineCostsFile = costModelDataDir </> "cekMachineCosts" <.> "json"
