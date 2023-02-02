{-# LANGUAGE DerivingVia      #-}
{-# LANGUAGE TypeApplications #-}
module PlutusLedgerApi.V3.EvaluationContext
    ( EvaluationContext
    , mkEvaluationContext
    , CostModelParams
    , assertWellFormedCostModelParams
    , toMachineParameters
    , CostModelApplyError (..)
    ) where

import PlutusCore.Default as Plutus (BuiltinVersion (DefaultFunV2))

import PlutusLedgerApi.Common
import PlutusLedgerApi.V3.ParamName as V3

import Control.Monad
import Control.Monad.Except
import Control.Monad.Writer.Strict

{-|  Build the 'EvaluationContext'.

The input is a list of integer values passed from the ledger and
are expected to appear in correct order.

IMPORTANT: The evaluation context of every Plutus version must be recreated upon a protocol update
with the updated cost model parameters.
-}
mkEvaluationContext :: (MonadError CostModelApplyError m, MonadWriter [CostModelApplyWarn] m)
                    => [Integer] -- ^ the (updated) cost model parameters of the protocol
                    -> m EvaluationContext
mkEvaluationContext = tagWithParamNames @V3.ParamName
                    >=> pure . toCostModelParams
                    >=> mkDynEvaluationContext Plutus.DefaultFunV2
