{-# LANGUAGE TypeApplications #-}
module PlutusLedgerApi.V2.EvaluationContext
    ( EvaluationContext
    , mkEvaluationContext
    , CostModelParams
    , assertWellFormedCostModelParams
    , toMachineParameters
    , CostModelApplyError (..)
    ) where

import PlutusLedgerApi.Common
import PlutusLedgerApi.V2.ParamName as V2

import PlutusCore.Default as Plutus (BuiltinSemanticsVariant (DefaultFunSemanticsVariant1))

import Control.Monad
import Control.Monad.Except
import Control.Monad.Writer.Strict

{-|  Build the 'EvaluationContext'.

The input is a list of cost model parameters (which are integer values) passed
from the ledger.

IMPORTANT: the cost model parameters __MUST__ appear in the correct order,
matching the names in `PlutusLedgerApi.V2.ParamName`.  If the parameters are
supplied in the wrong order then script cost calculations will be incorrect.

IMPORTANT: The evaluation context of every Plutus version must be recreated upon
a protocol update with the updated cost model parameters.
-}
mkEvaluationContext :: (MonadError CostModelApplyError m, MonadWriter [CostModelApplyWarn] m)
                    => [Integer] -- ^ the (updated) cost model parameters of the protocol
                    -> m EvaluationContext
mkEvaluationContext = tagWithParamNames @V2.ParamName
                    >=> pure . toCostModelParams
                    >=> mkDynEvaluationContext Plutus.DefaultFunSemanticsVariant1
