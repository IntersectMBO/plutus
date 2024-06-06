-- editorconfig-checker-disable
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
import PlutusLedgerApi.Common.Versions (conwayPV)
import PlutusLedgerApi.V2.ParamName as V2

import PlutusCore.Default (BuiltinSemanticsVariant (DefaultFunSemanticsVariantA, DefaultFunSemanticsVariantB))

import Control.Monad
import Control.Monad.Writer.Strict
import Data.Int (Int64)

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
                    => [Int64] -- ^ the (updated) cost model parameters of the protocol
                    -> m EvaluationContext
mkEvaluationContext =
    tagWithParamNames @V2.ParamName
    >=> pure . toCostModelParams
    >=> mkDynEvaluationContext
        PlutusV2
        [DefaultFunSemanticsVariantA, DefaultFunSemanticsVariantB]
        -- See Note [Mapping of protocol versions and ledger languages to semantics variants].
        (\pv -> if pv < conwayPV
            then DefaultFunSemanticsVariantA
            else DefaultFunSemanticsVariantB)
