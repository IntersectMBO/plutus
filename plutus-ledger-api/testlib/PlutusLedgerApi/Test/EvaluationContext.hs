-- editorconfig-checker-disable-file
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
module PlutusLedgerApi.Test.EvaluationContext
    ( v1_costModelParamsForTesting
    , v2_costModelParamsForTesting
    , v3_costModelParamsForTesting
    ) where

import PlutusCore.Evaluation.Machine.BuiltinCostModel
import PlutusCore.Evaluation.Machine.CostModelInterface
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusPrelude
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts

import PlutusLedgerApi.Common as Common
import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V2 qualified as V2
import PlutusLedgerApi.V3 qualified as V3

import Barbies
import Data.Aeson
import Data.Functor.Identity
import Data.Map qualified as Map
import Data.Maybe

-- | Example values of costs for plutus-v3 , in expected ledger order, i.e. can be used in testing
-- `V3.mkEvaluationContext . fmap snd`
v3_costModelParamsForTesting :: [(V3.ParamName, Integer)]
v3_costModelParamsForTesting = Map.toList $ fromJust $ extractCostModelParamsLedgerOrder v3_liftedCostModel

-- | Example values of costs for plutus-v2, in expected ledger order, i.e. can be used in testing
-- `V2.mkEvaluationContext . fmap snd`
v2_costModelParamsForTesting :: [(V2.ParamName,Integer)]
v2_costModelParamsForTesting = Map.toList $ fromJust $ extractCostModelParamsLedgerOrder v2_liftedCostModel

-- | Example values of costs for plutus-v1, *in expected ledger order*, i.e. can be used in testing
-- `V1.mkEvaluationContext . fmap snd`
v1_costModelParamsForTesting :: [(V1.ParamName,Integer)]
v1_costModelParamsForTesting = Map.toList $ fromJust $ extractCostModelParamsLedgerOrder v1_liftedCostModel

v3_liftedCostModel, v2_liftedCostModel, v1_liftedCostModel
    :: CostModel (CekMachineCostsBase Maybe)  (BuiltinCostModelBase MCostingFun)
v3_liftedCostModel = liftToJust defaultCekCostModel
v2_liftedCostModel = v3_liftedCostModel
                    & machineCostModel
                    %~ clearV3machineCostModel
                    & builtinCostModel
                    %~ clearV3builtinCostModel
v1_liftedCostModel = v2_liftedCostModel
                    & builtinCostModel
                    %~ clearV2builtinCostModel

-- Assign to `mempty` those builtins that the specific plutus version X introduces, and thus
-- are missing from version X-1.
-- Calling this function on a vX_BuiltinCostModel will turn it into a vX-1_BuiltinCostModel,
-- by omitting the generation of costs concerning the missing builtins.
clearV3builtinCostModel, clearV2builtinCostModel
    :: (m ~ BuiltinCostModelBase MCostingFun) => m -> m
clearV3builtinCostModel r = r
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
clearV2builtinCostModel r = r
               { paramSerialiseData = mempty
               , paramVerifyEcdsaSecp256k1Signature = mempty
               , paramVerifySchnorrSecp256k1Signature = mempty
               }

-- Assign to `mempty` those CEK construct that the specific plutus version X introduces, and thus
-- are missing from version X-1.
-- Calling this function on a vX_CekMachineCosts will turn it into a vX-1_CekMachineCosts,
-- by omitting the generation of costs concerning the missing CEK constructs.
clearV3machineCostModel :: (m ~ CekMachineCostsBase Maybe) => m -> m
clearV3machineCostModel r = r
    { cekConstrCost  = mempty
    , cekCaseCost    = mempty
    }

-- Helpers

-- A variant of `extractCostModelParams` that returns the `CostModelParams` not in alphabetical order,
-- but in the `ParamName` order, i.e. the order expected by the ledger
extractCostModelParamsLedgerOrder :: (Common.IsParamName p, Ord p, ToJSON machinecosts, ToJSON builtincosts)
                     => CostModel machinecosts builtincosts
                     -> Maybe (Map.Map p Integer)
extractCostModelParamsLedgerOrder cm =
    let mapInAlphaOrder = extractCostModelParams cm
        mapInLedgerOrder = Map.mapKeys (fromJust . readParamName) <$> mapInAlphaOrder
    in mapInLedgerOrder

-- A helper function that barbie-composes with `Maybe` functor, so that specific fields can be
-- omitted via `mempty`.
liftToJust :: CostModel CekMachineCosts BuiltinCostModel
           -> CostModel (CekMachineCostsBase Maybe)  (BuiltinCostModelBase MCostingFun)
liftToJust cm =
   cm
   & machineCostModel
   %~ bmap (Just . runIdentity)
   & builtinCostModel
   %~ bmap (MCostingFun . Just)
