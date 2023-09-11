{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
module PlutusLedgerApi.Test.V3.EvaluationContext
    ( costModelParamsForTesting
    , mCostModel
    , clearMachineCostModel
    , clearBuiltinCostModel
    ) where

import PlutusCore.Evaluation.Machine.BuiltinCostModel
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusLedgerApi.Test.Common.EvaluationContext as Common
import PlutusLedgerApi.V3 qualified as V3
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts

import Data.Map qualified as Map
import Data.Maybe

-- | Example values of costs for @PlutusV3@, in expected ledger order.
-- Suitable to be used in testing.
costModelParamsForTesting :: [(V3.ParamName, Integer)]
costModelParamsForTesting = Map.toList $ fromJust $
    Common.extractCostModelParamsLedgerOrder mCostModel

-- | The PlutusV3 "cost model" is constructed by the v4 "cost model", by clearing v4 introductions.
mCostModel :: MCostModel
mCostModel =
    -- nothing to clear because v4 does not exist (yet).
    toMCostModel defaultCekCostModel

{- | Assign to `mempty` those CEK constructs that @PlutusV3@ introduces (indirectly by introducing
a ledger language version with those CEK constructs).

This can be used to generate a (machine) cost model of the previous plutus version,
by omitting the generation of the costs concerning the missing @PlutusV3@ CEK constructs.
-}
clearMachineCostModel :: (m ~ MCekMachineCosts) => m -> m
clearMachineCostModel r = r
    { cekConstrCost  = mempty
    , cekCaseCost    = mempty
    }

{- | Assign to `mempty` those builtins that the @PlutusV3@ introduces.

This can be used to generate a (builtin) cost model of the previous version
by omitting the generation of the costs concerning the missing @PlutusV3@ builtins.
-}
clearBuiltinCostModel :: (m ~ MBuiltinCostModel) => m -> m
clearBuiltinCostModel r = r
               { paramBls12_381_G1_add = mempty
               , paramBls12_381_G1_neg = mempty
               , paramBls12_381_G1_scalarMul = mempty
               , paramBls12_381_G1_equal = mempty
               , paramBls12_381_G1_hashToGroup = mempty
               , paramBls12_381_G1_compress = mempty
               , paramBls12_381_G1_uncompress = mempty
               , paramBls12_381_G2_add = mempty
               , paramBls12_381_G2_neg = mempty
               , paramBls12_381_G2_scalarMul = mempty
               , paramBls12_381_G2_equal = mempty
               , paramBls12_381_G2_hashToGroup = mempty
               , paramBls12_381_G2_compress = mempty
               , paramBls12_381_G2_uncompress = mempty
               , paramBls12_381_millerLoop = mempty
               , paramBls12_381_mulMlResult = mempty
               , paramBls12_381_finalVerify = mempty
               , paramKeccak_256 = mempty
               , paramBlake2b_224 = mempty
               }
