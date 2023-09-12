{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}
module PlutusLedgerApi.Test.V1.EvaluationContext
    ( costModelParamsForTesting
    , mCostModel
    , clearMachineCostModel
    , clearBuiltinCostModel
    ) where

import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusLedgerApi.Test.Common.EvaluationContext as Common
import PlutusLedgerApi.Test.V2.EvaluationContext qualified as V2
import PlutusLedgerApi.V1 qualified as V1
import PlutusPrelude

import Data.Map qualified as Map
import Data.Maybe

-- | Example values of costs for @PlutusV1@, in expected ledger order.
-- Suitable to be used in testing.
costModelParamsForTesting :: [(V1.ParamName, Integer)]
costModelParamsForTesting = Map.toList $ fromJust $
    Common.extractCostModelParamsLedgerOrder mCostModel

-- | The PlutusV1 "cost model" is constructed by the v2 "cost model", by clearing v2 introductions.
mCostModel :: MCostModel
mCostModel = V2.mCostModel
           & machineCostModel
           %~ V2.clearMachineCostModel -- no changes for machine costs, so this is id
           & builtinCostModel
           %~ V2.clearBuiltinCostModel

{- | Assign to `mempty` those CEK constructs that @PlutusV1@ introduces (indirectly by introducing
a ledger language version with those CEK constructs).

This can be used to generate a (machine) cost model of the previous plutus version,
by omitting the generation of the costs concerning the missing @PlutusV1@ CEK constructs.
-}
clearMachineCostModel :: (m ~ MCekMachineCosts) => m -> m
clearMachineCostModel = id -- no PlutusV0 so nothing to clear

{- | Assign to `mempty` those builtins that the @PlutusV1@ introduces.

This can be used to generate a (builtin) cost model of the previous version
by omitting the generation of the costs concerning the missing @PlutusV1@ builtins.
-}
clearBuiltinCostModel :: (m ~ MBuiltinCostModel) => m -> m
clearBuiltinCostModel = id -- no PlutusV0 so nothing to clear
