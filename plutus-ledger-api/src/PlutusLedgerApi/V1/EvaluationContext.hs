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

import PlutusCore.Default as Plutus (BuiltinVersion (DefaultFunV1))
import PlutusCore.Evaluation.Machine.CostModelInterface as Plutus

import Control.Monad
import Control.Monad.Except
import Control.Monad.Writer.Strict

{-|  Build the 'EvaluationContext'.

The input is a list of integer values passed from the ledger and
are expected to appear in correct order.
-}
mkEvaluationContext :: (MonadError CostModelApplyError m, MonadWriter [CostModelApplyWarn] m)
                    => [Integer] -> m EvaluationContext
mkEvaluationContext = tagWithParamNames @V1.ParamName
                    >=> pure . toCostModelParams
                    >=> mkDynEvaluationContext Plutus.DefaultFunV1
