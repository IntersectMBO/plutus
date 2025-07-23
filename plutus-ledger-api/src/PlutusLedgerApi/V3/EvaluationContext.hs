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

import PlutusCore.Builtin (CaserBuiltin (..), caseBuiltin, unavailableCaserBuiltin)
import PlutusCore.Default (BuiltinSemanticsVariant (DefaultFunSemanticsVariantC))

import Control.Monad
import Control.Monad.Writer.Strict
import Data.Int (Int64)

{-|  Build the 'EvaluationContext'.

The input is a list of cost model parameters (which are integer values) passed
from the ledger.

IMPORTANT: the cost model parameters __MUST__ appear in the correct order,
matching the names in `PlutusLedgerApi.V3.ParamName`.  If the parameters are
supplied in the wrong order then script cost calculations will be incorrect.

IMPORTANT: The evaluation context of every Plutus version must be recreated upon
a protocol update with the updated cost model parameters.
-}
mkEvaluationContext
  :: (MonadError CostModelApplyError m, MonadWriter [CostModelApplyWarn] m)
  => [Int64] -- ^ the (updated) cost model parameters of the protocol
  -> m EvaluationContext
mkEvaluationContext =
  tagWithParamNames @V3.ParamName
    >=> pure . toCostModelParams
    >=> mkDynEvaluationContext
        PlutusV3
        (\pv ->
          if pv < pv11PV
            then unavailableCaserBuiltin $ getMajorProtocolVersion pv
            else CaserBuiltin caseBuiltin)
        [DefaultFunSemanticsVariantC]
        -- See Note [Mapping of protocol versions and ledger languages to semantics variants].
        (const DefaultFunSemanticsVariantC)
