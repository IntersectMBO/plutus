{-# LANGUAGE TypeApplications #-}
module PlutusLedgerApi.V2.Eval
    ( module PlutusLedgerApi.Common.Versions
    , module PlutusLedgerApi.Internal.Eval
    , evaluateScriptRestricting
    , evaluateScriptCounting
    , mkEvaluationContext
    ) where

import PlutusLedgerApi.Common.Versions
import PlutusLedgerApi.Internal.Eval
    hiding ( evaluateScriptCounting
           , evaluateScriptRestricting
           , mkDynEvaluationContext
           )
import PlutusLedgerApi.Internal.Eval qualified as Internal

import PlutusLedgerApi.Common.SerialisedScript
import PlutusCore.Evaluation.Machine.ExBudget as PLC
import PlutusCore.Data qualified as PLC

import PlutusLedgerApi.Internal.IsParamName
import PlutusLedgerApi.V2.ParamName as V2

import PlutusCore.Default as Plutus (BuiltinVersion (DefaultFunV1))

import Control.Monad
import Control.Monad.Except
import Control.Monad.Writer.Strict


-- | Evaluates a script, returning the minimum budget that the script would need
-- to evaluate successfully. This will take as long as the script takes, if you need to
-- limit the execution time of the script also, you can use 'evaluateScriptRestricting', which
-- also returns the used budget.
evaluateScriptCounting
    :: ProtocolVersion
    -> VerboseMode     -- ^ Whether to produce log output
    -> EvaluationContext -- ^ The cost model that should already be synced to the most recent cost-model-params coming from the current protocol
    -> SerialisedScript          -- ^ The script to evaluate
    -> [PLC.Data]          -- ^ The arguments to the script
    -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptCounting = Internal.evaluateScriptCounting PlutusV2

-- | Evaluates a script, with a cost model and a budget that restricts how many
-- resources it can use according to the cost model. Also returns the budget that
-- was actually used.
--
-- Can be used to calculate budgets for scripts, but even in this case you must give
-- a limit to guard against scripts that run for a long time or loop.
evaluateScriptRestricting
    :: ProtocolVersion
    -> VerboseMode     -- ^ Whether to produce log output
    -> EvaluationContext -- ^ The cost model that should already be synced to the most recent cost-model-params coming from the current protocol
    -> ExBudget        -- ^ The resource budget which must not be exceeded during evaluation
    -> SerialisedScript          -- ^ The script to evaluate
    -> [PLC.Data]          -- ^ The arguments to the script
    -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptRestricting = Internal.evaluateScriptRestricting PlutusV2


{-|  Build the 'EvaluationContext'.

The input is a list of integer values passed from the ledger and
are expected to appear in correct order.
-}
mkEvaluationContext :: (MonadError CostModelApplyError m, MonadWriter [CostModelApplyWarn] m)
                    => [Integer] -> m EvaluationContext
mkEvaluationContext = tagWithParamNames @V2.ParamName
                    >=> pure . unTagParamNames
                    >=> Internal.mkDynEvaluationContext Plutus.DefaultFunV1
