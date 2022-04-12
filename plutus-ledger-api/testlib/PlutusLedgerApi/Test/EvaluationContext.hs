module PlutusLedgerApi.Test.EvaluationContext
    ( costModelParamsForTesting
    , evalCtxForTesting
    ) where

import PlutusCore.Evaluation.Machine.CostModelInterface as Plutus
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as Plutus
import PlutusLedgerApi.Common

import Control.Exception
import Data.Maybe

-- | The raw cost model params, only to be used for testing purposes.
costModelParamsForTesting :: Plutus.CostModelParams
costModelParamsForTesting = fromJust Plutus.defaultCostModelParams

-- | only to be for testing purposes: make an evaluation context by applying an empty set of protocol parameters
evalCtxForTesting :: EvaluationContext
evalCtxForTesting = either throw id $ mkDynEvaluationContext costModelParamsForTesting
