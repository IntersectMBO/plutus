{-| Various file paths used in plutus-core.
    These paths are primarily used for testing and benchmarking.
    Cost models are embedded as Haskell modules in
    PlutusCore.Evaluation.Machine.CostModel.Generated.* -}
module PlutusCore.DataFilePaths
where

import System.FilePath

costModelDataDir :: FilePath
costModelDataDir = "cost-model" </> "data"

-- | The file containing the R models: needed for cost-model-test and generate-cost-model.
rModelFile :: FilePath
rModelFile = costModelDataDir </> "models" <.> "R"

{-| The file containing the benchmark results for the built-in functions:
needed for cost-model-test and generate-cost-model. -}
benchingResultsFile :: FilePath
benchingResultsFile = costModelDataDir </> "benching-conway" <.> "csv"
