{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeApplications #-}
module PlutusLedgerApi.V3.EvaluationContext
    ( EvaluationContext
    , mkEvaluationContext
    , CostModelParams
    , assertWellFormedCostModelParams
    , toMachineParameters
    , CostModelApplyError (..)
    ) where

import PlutusLedgerApi.Common
import PlutusLedgerApi.V3.ParamName as V3

import PlutusCore.Default as Plutus (BuiltinSemanticsVariant (DefaultFunSemanticsVariant2))
import PlutusCore.Evaluation.Machine.MachineParameters.Default (SubDefaultFunSemanticsVariant (..))

import Control.Monad
import Control.Monad.Except
import Control.Monad.Writer.Strict

data DefaultFunSemanticsVariant_V3
    = DefaultFunSemanticsVariant2_V3
    deriving stock (Bounded, Enum)

instance SubDefaultFunSemanticsVariant DefaultFunSemanticsVariant_V3 where
    toDefaultFunSemanticsVariant DefaultFunSemanticsVariant2_V3 = DefaultFunSemanticsVariant2

    memoSemVarM f = do
        r2 <- f DefaultFunSemanticsVariant2_V3
        pure $ \case
            DefaultFunSemanticsVariant2_V3 -> r2

{-|  Build the 'EvaluationContext'.

The input is a list of cost model parameters (which are integer values) passed
from the ledger.

IMPORTANT: the cost model parameters __MUST__ appear in the correct order,
matching the names in `PlutusLedgerApi.V3.ParamName`.  If the parameters are
supplied in the wrong order then script cost calculations will be incorrect.

IMPORTANT: The evaluation context of every Plutus version must be recreated upon
a protocol update with the updated cost model parameters.
-}
mkEvaluationContext :: (MonadError CostModelApplyError m, MonadWriter [CostModelApplyWarn] m)
                    => [Integer] -- ^ the (updated) cost model parameters of the protocol
                    -> m EvaluationContext
mkEvaluationContext =
    tagWithParamNames @V3.ParamName
    >=> pure . toCostModelParams
    >=> mkDynEvaluationContext
        (const DefaultFunSemanticsVariant2_V3)
