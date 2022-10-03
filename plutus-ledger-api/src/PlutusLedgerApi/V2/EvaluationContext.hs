{-# LANGUAGE DerivingVia      #-}
{-# LANGUAGE TypeApplications #-}
module PlutusLedgerApi.V2.EvaluationContext
    ( EvaluationContext
    , mkEvaluationContext
    ) where

import PlutusLedgerApi.Internal.EvaluationContext
import PlutusLedgerApi.Internal.ParamName
import PlutusLedgerApi.V2.ParamName as V2

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
mkEvaluationContext = tagWithParamNames @V2.ParamName
                    >=> pure . unTagParamNames
                    >=> mkDynEvaluationContext Plutus.DefaultFunV1
