-- editorconfig-checker-disable-file
{-# LANGUAGE TypeApplications #-}
module PlutusLedgerApi.V1.EvaluationContext
    ( EvaluationContext
    , mkEvaluationContext
    , CostModelParams
    , assertWellFormedCostModelParams
    , machineParametersImmediate
    , machineParametersDeferred
    , toMachineParameters
    , CostModelApplyError (..)
    ) where

import PlutusLedgerApi.Common
import PlutusLedgerApi.V1.ParamName as V1

import PlutusCore.Evaluation.Machine.CostModelInterface as Plutus

import Control.Monad
import Control.Monad.Except

{-|  Build the 'EvaluationContext'.

The input is a list of integer values passed from the ledger and are expected to appear in correct order.
-}
mkEvaluationContext :: MonadError CostModelApplyError m => [Integer] -> m EvaluationContext
mkEvaluationContext = mkDynEvaluationContext . toCostModelParams <=< tagWithParamNames @V1.ParamName
