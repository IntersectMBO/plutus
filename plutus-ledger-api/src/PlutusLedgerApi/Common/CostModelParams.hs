module PlutusLedgerApi.Common.CostModelParams
    ( assertWellFormedCostModelParams
    , CostModelParams
    , CostModelApplyError (..)
    ) where

import PlutusCore.Evaluation.Machine.CostModelInterface
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import Control.Monad.Except

--- | Comparably expensive to `mkDynEvaluationContext`, so it should only be used sparingly.
assertWellFormedCostModelParams :: MonadError CostModelApplyError m => CostModelParams -> m ()
assertWellFormedCostModelParams = void . applyCostModelParams defaultCekCostModel
