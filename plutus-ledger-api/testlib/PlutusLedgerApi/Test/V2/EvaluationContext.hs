{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}
module PlutusLedgerApi.Test.V2.EvaluationContext
    ( costModelParamsForTesting
    , mCostModel
    , clearMachineCostModel
    , clearBuiltinCostModel
    ) where

import PlutusCore.Evaluation.Machine.BuiltinCostModel
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusLedgerApi.Test.Common.EvaluationContext as Common
import PlutusLedgerApi.Test.V3.EvaluationContext qualified as V3
import PlutusLedgerApi.V2 qualified as V2
import PlutusPrelude

import Data.Map qualified as Map
import Data.Maybe

-- | Example values of costs for @PlutusV2@, in expected ledger order.
-- Suitable to be used in testing.
costModelParamsForTesting :: [(V2.ParamName, Integer)]
costModelParamsForTesting = Map.toList $ fromJust $
    Common.extractCostModelParamsLedgerOrder mCostModel

-- | The PlutusV2 "cost model" is constructed by the v3 "cost model", by clearing v3 introductions.
mCostModel :: MCostModel
mCostModel = V3.mCostModel
           & machineCostModel
           %~ V3.clearMachineCostModel
           & builtinCostModel
           %~ V3.clearBuiltinCostModel

{- | Assign to `mempty` those CEK constructs that @PlutusV2@ introduces (indirectly by introducing
a ledger language version with those CEK constructs).

This can be used to generate a (machine) cost model of the previous plutus version,
by omitting the generation of the costs concerning the missing @PlutusV2@ CEK constructs.
-}
clearMachineCostModel :: (m ~ MCekMachineCosts) => m -> m
clearMachineCostModel = id -- nothing changed, so nothing to clear

{- | Assign to `mempty` those builtins that the @PlutusV2@ introduces.

This can be used to generate a (builtin) cost model of the previous version
by omitting the generation of the costs concerning the missing @PlutusV2@ builtins.
-}
clearBuiltinCostModel :: (m ~ MBuiltinCostModel) => m -> m
clearBuiltinCostModel r = r
               { paramSerialiseData = mempty
               , paramVerifyEcdsaSecp256k1Signature = mempty
               , paramVerifySchnorrSecp256k1Signature = mempty
               }
