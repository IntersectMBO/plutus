-- editorconfig-checker-disable
{-# LANGUAGE LambdaCase       #-}
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

import PlutusCore.Default as Plutus (BuiltinSemanticsVariant (DefaultFunSemanticsVariant0, DefaultFunSemanticsVariant1))
import PlutusCore.Evaluation.Machine.MachineParameters.Default (SubDefaultFunSemanticsVariant (..))

import Control.Monad
import Control.Monad.Except
import Control.Monad.Writer.Strict

data DefaultFunSemanticsVariant_V2
    = DefaultFunSemanticsVariant0_V2
    | DefaultFunSemanticsVariant1_V2
    deriving stock (Bounded, Enum)

instance SubDefaultFunSemanticsVariant DefaultFunSemanticsVariant_V2 where
    toDefaultFunSemanticsVariant DefaultFunSemanticsVariant0_V2 = DefaultFunSemanticsVariant0
    toDefaultFunSemanticsVariant DefaultFunSemanticsVariant1_V2 = DefaultFunSemanticsVariant1

    memoSemVarM f = do
        r0 <- f DefaultFunSemanticsVariant0_V2
        r1 <- f DefaultFunSemanticsVariant1_V2
        pure $ \case
            DefaultFunSemanticsVariant0_V2 -> r0
            DefaultFunSemanticsVariant1_V2 -> r1

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
mkEvaluationContext =
    tagWithParamNames @V2.ParamName
    >=> pure . toCostModelParams
    >=> mkDynEvaluationContext
        (\pv -> if pv < conwayPV
            then DefaultFunSemanticsVariant0_V2
            else DefaultFunSemanticsVariant1_V2)
