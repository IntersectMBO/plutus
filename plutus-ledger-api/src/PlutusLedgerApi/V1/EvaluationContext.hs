-- editorconfig-checker-disable
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
import PlutusLedgerApi.V1.ParamName as V1

import PlutusCore.Builtin (CaserBuiltin (..), caseBuiltin, unavailableCaserBuiltin)
import PlutusCore.Default (BuiltinSemanticsVariant (DefaultFunSemanticsVariantA, DefaultFunSemanticsVariantB))

import Control.Monad
import Control.Monad.Writer.Strict
import Data.Int (Int64)

{-|  Build the 'EvaluationContext'.

The input is a list of cost model parameters (which are integer values) passed
from the ledger.

IMPORTANT: the cost model parameters __MUST__ appear in the correct order,
matching the names in `PlutusLedgerApi.V1.ParamName`.  If the parameters are
supplied in the wrong order then script cost calculations will be incorrect.

IMPORTANT: The evaluation context of every Plutus version must be recreated upon
a protocol update with the updated cost model parameters. -}
mkEvaluationContext
  :: (MonadError CostModelApplyError m, MonadWriter [CostModelApplyWarn] m)
  => [Int64]
  -- ^ the (updated) cost model parameters of the protocol
  -> m EvaluationContext
mkEvaluationContext =
  tagWithParamNames @V1.ParamName
    >=> pure . toCostModelParams
    >=> mkDynEvaluationContext
      PlutusV1
      ( \pv ->
          if pv < pv11PV
            then unavailableCaserBuiltin $ getMajorProtocolVersion pv
            else CaserBuiltin caseBuiltin
      )
      [DefaultFunSemanticsVariantA, DefaultFunSemanticsVariantB]
      -- See Note [Mapping of protocol versions and ledger languages to semantics variants].
      ( \pv ->
          if pv < changPV
            then DefaultFunSemanticsVariantA
            else DefaultFunSemanticsVariantB
      )
