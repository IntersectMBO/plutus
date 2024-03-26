-- editorconfig-checker-disable
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeApplications #-}
module PlutusLedgerApi.V1.EvaluationContext
    ( EvaluationContext
    , mkEvaluationContext
    , CostModelParams
    , assertWellFormedCostModelParams
    , toMachineParameters
    , CostModelApplyError (..)
    ) where

import PlutusLedgerApi.Common
import PlutusLedgerApi.Common.Versions (conwayPV)
import PlutusLedgerApi.V1.ParamName as V1

import PlutusCore.Default (BuiltinSemanticsVariant (DefaultFunSemanticsVariant0, DefaultFunSemanticsVariant1))
import PlutusCore.Evaluation.Machine.MachineParameters.Default (SubDefaultFunSemanticsVariant (..))

import Control.Monad
import Control.Monad.Except
import Control.Monad.Writer.Strict

data DefaultFunSemanticsVariant_V1
    = DefaultFunSemanticsVariant0_V1
    | DefaultFunSemanticsVariant1_V1
    deriving stock (Bounded, Enum)

instance SubDefaultFunSemanticsVariant DefaultFunSemanticsVariant_V1 where
    toDefaultFunSemanticsVariant DefaultFunSemanticsVariant0_V1 = DefaultFunSemanticsVariant0
    toDefaultFunSemanticsVariant DefaultFunSemanticsVariant1_V1 = DefaultFunSemanticsVariant1

    memoSemVarM f = do
        r0 <- f DefaultFunSemanticsVariant0_V1
        r1 <- f DefaultFunSemanticsVariant1_V1
        pure $ \case
            DefaultFunSemanticsVariant0_V1 -> r0
            DefaultFunSemanticsVariant1_V1 -> r1

{-|  Build the 'EvaluationContext'.

The input is a list of cost model parameters (which are integer values) passed
from the ledger.

IMPORTANT: the cost model parameters __MUST__ appear in the correct order,
matching the names in `PlutusLedgerApi.V1.ParamName`.  If the parameters are
supplied in the wrong order then script cost calculations will be incorrect.

IMPORTANT: The evaluation context of every Plutus version must be recreated upon
a protocol update with the updated cost model parameters.
-}
mkEvaluationContext :: (MonadError CostModelApplyError m, MonadWriter [CostModelApplyWarn] m)
                    => [Integer] -- ^ the (updated) cost model parameters of the protocol
                    -> m EvaluationContext
mkEvaluationContext =
    tagWithParamNames @V1.ParamName
    >=> pure . toCostModelParams
    >=> mkDynEvaluationContext
        (\pv -> if pv < conwayPV
            then DefaultFunSemanticsVariant0_V1
            else DefaultFunSemanticsVariant1_V1)
