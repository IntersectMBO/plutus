module Plutus.Ledger.Test.EvaluationContext
    ( costModelParamsForTesting
    , evalCtxForTesting
    ) where

import Plutus.V1.Ledger.EvaluationContext
import PlutusCore.Evaluation.Machine.CostModelInterface as Plutus
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as Plutus

import Data.Maybe

-- | The raw cost model params, only to be used for testing purposes.
costModelParamsForTesting :: Plutus.CostModelParams
costModelParamsForTesting = fromJust Plutus.defaultCostModelParams

-- | only to be for testing purposes: make an evaluation context by applying an empty set of protocol parameters
evalCtxForTesting :: EvaluationContext
evalCtxForTesting = fromJust $ mkEvaluationContext mempty
