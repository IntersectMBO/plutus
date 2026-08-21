{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

module PlutusLedgerApi.Test.V4.EvaluationContext
  ( costModelParamsForTesting
  , mCostModel
  , clearMachineCostModel
  , clearBuiltinCostModel
  ) where

import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusLedgerApi.Test.Common.EvaluationContext as Common
import PlutusLedgerApi.V4 qualified as V4

import Data.Int (Int64)
import Data.Map qualified as Map
import GHC.Stack (HasCallStack)

{-| Example values of costs for @PlutusV4@, in expected ledger order.
Suitable to be used in testing. -}
costModelParamsForTesting :: HasCallStack => [(V4.ParamName, Int64)]
costModelParamsForTesting =
  case Common.extractCostModelParamsLedgerOrder mCostModel of
    Nothing -> error "extractCostModelParamsLedgerOrder (V4): nothing extracted"
    Just xs -> Map.toList xs

{-| The PlutusV4 "cost model" is the full cost model: there is no later ledger
language whose introductions would have to be cleared. -}
mCostModel :: MCostModel
mCostModel = toMCostModel defaultCekCostModelForTesting

{-| Assign to `mempty` those CEK constructs that @PlutusV4@ introduces (indirectly by introducing
a ledger language version with those CEK constructs).

This can be used to generate a (machine) cost model of the previous plutus version,
by omitting the generation of the costs concerning the missing @PlutusV4@ CEK constructs. -}
clearMachineCostModel :: m ~ MCekMachineCosts => m -> m
clearMachineCostModel = id -- PlutusV4 introduces no new CEK constructs

{-| Assign to `mempty` those builtins that the @PlutusV4@ introduces.

This can be used to generate a (builtin) cost model of the previous version
by omitting the generation of the costs concerning the missing @PlutusV4@ builtins. -}
clearBuiltinCostModel :: m ~ MBuiltinCostModel => m -> m
clearBuiltinCostModel = id -- PlutusV4 introduces no new builtins
