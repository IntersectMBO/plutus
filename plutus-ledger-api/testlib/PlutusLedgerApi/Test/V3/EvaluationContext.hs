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
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusLedgerApi.Test.Common.EvaluationContext as Common
import PlutusLedgerApi.V3 qualified as V3
import PlutusPrelude
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts


import Data.Int (Int64)
import Data.Map qualified as Map
import Data.Maybe
import GHC.Stack (HasCallStack)


-- ** FIXME **. These tests no longer make much sense because now we're assuming
-- that all builtins will be available in all PlutusVN, so the cost models will
-- be very similar (but not yet identical).

-- | Example values of costs for @PlutusV3@, in expected ledger order.
-- Suitable to be used in testing.
costModelParamsForTesting :: HasCallStack => [(V3.ParamName, Int64)]
costModelParamsForTesting = Map.toList $ fromJust $
    Common.extractCostModelParamsLedgerOrder mCostModel

-- | The PlutusV3 "cost model" is constructed by the v4 "cost model", by clearing v4 introductions.
mCostModel :: MCostModel
mCostModel =
    -- nothing to clear because v4 does not exist (yet).
    toMCostModel defaultCekCostModelForTesting & builtinCostModel %~ clearBuiltinCostModel'

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
               , paramIntegerToByteString = mempty
               , paramByteStringToInteger = mempty
               , paramAndByteString = mempty
               , paramOrByteString = mempty
               , paramXorByteString = mempty
               , paramComplementByteString = mempty
               , paramReadBit = mempty
               , paramWriteBits = mempty
               , paramReplicateByte = mempty
               , paramShiftByteString = mempty
               , paramRotateByteString = mempty
               , paramCountSetBits = mempty
               , paramFindFirstSetBit = mempty
               , paramRipemd_160 = mempty
               , paramExpModInteger = mempty
               , paramDropList = mempty
               , paramLengthOfArray = mempty
               , paramListToArray = mempty
               , paramIndexArray = mempty
               }


-- *** FIXME(https://github.com/IntersectMBO/plutus-private/issues/1610)!!! ***
-- This is temporary to get the tests to pass
-- [Later: now we can get away without this because we're planning to deploy all builtins in all versions].
clearBuiltinCostModel' ::
  -- (m ~ MBuiltinCostModel) =>
  m -> m
clearBuiltinCostModel' r = r
