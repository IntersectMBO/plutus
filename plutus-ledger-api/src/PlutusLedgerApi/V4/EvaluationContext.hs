{-# LANGUAGE TypeApplications #-}

module PlutusLedgerApi.V4.EvaluationContext
  ( EvaluationContext
  , mkEvaluationContext
  , CostModelParams
  , assertWellFormedCostModelParams
  , toMachineParameters
  , CostModelApplyError (..)
  ) where

import PlutusLedgerApi.Common
import PlutusLedgerApi.V4.ParamName as V4

import PlutusCore.Builtin (CaserBuiltin (..), caseBuiltin)
import PlutusCore.Default (BuiltinSemanticsVariant (DefaultFunSemanticsVariantE))

import Control.Monad
import Control.Monad.Writer.Strict
import Data.Int (Int64)

{-|  Build the 'EvaluationContext'.

The input is a list of cost model parameters (which are integer values) passed
from the ledger.

IMPORTANT: the cost model parameters __MUST__ appear in the correct order,
matching the names in `PlutusLedgerApi.V4.ParamName`.  If the parameters are
supplied in the wrong order then script cost calculations will be incorrect.

IMPORTANT: The evaluation context of every Plutus version must be recreated upon
a protocol update with the updated cost model parameters. -}
mkEvaluationContext
  :: (MonadError CostModelApplyError m, MonadWriter [CostModelApplyWarn] m)
  => [Int64]
  -- ^ the (updated) cost model parameters of the protocol
  -> m EvaluationContext
mkEvaluationContext =
  tagWithParamNames @V4.ParamName
    >=> pure . toCostModelParams
    >=> mkDynEvaluationContext
      PlutusV4
      -- 'PlutusV4' is introduced at the Dijkstra HF, so casing on builtins is always available.
      (\_ -> CaserBuiltin caseBuiltin)
      [DefaultFunSemanticsVariantE]
      -- See Note [Mapping of protocol versions and ledger languages to semantics variants].
      (\_ -> DefaultFunSemanticsVariantE)
