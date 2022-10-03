{-# LANGUAGE DerivingVia      #-}
{-# LANGUAGE TypeApplications #-}
module PlutusLedgerApi.V3.EvaluationContext
    ( EvaluationContext
    , mkEvaluationContext
    , CostModelParams
    , assertWellFormedCostModelParams
    , CostModelApplyError (..)
    ) where

import PlutusLedgerApi.Common
import PlutusLedgerApi.Internal.ParamName
import PlutusLedgerApi.V3.ParamName as V3

import PlutusCore.Default as Plutus (BuiltinVersion (DefaultFunV2))
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
mkEvaluationContext = tagWithParamNames @V3.ParamName
                    >=> pure . unTagParamNames
                    >=> mkDynEvaluationContext Plutus.DefaultFunV2
