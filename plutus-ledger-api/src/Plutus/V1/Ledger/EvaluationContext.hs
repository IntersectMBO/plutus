module Plutus.V1.Ledger.EvaluationContext
    ( EvaluationContext
    , mkEvaluationContext
    , CostModelParams
    , isCostModelParamsWellFormed
    , toMachineParameters
    , costModelParamNames
    , costModelParamsForTesting
    , evalCtxForTesting
    ) where

import PlutusCore as Plutus (DefaultFun, DefaultUni, defaultCekCostModel, defaultCostModelParams)
import PlutusCore.Evaluation.Machine.CostModelInterface as Plutus
import PlutusCore.Evaluation.Machine.MachineParameters as Plutus
import UntypedPlutusCore.Evaluation.Machine.Cek as Plutus

import Data.Map as Map
import Data.Maybe
import Data.Set as Set
import Data.Text qualified as Text

-- | An opaque type that contains all the static parameters that the evaluator needs to evaluate a script.
-- This is so that they can be computed once and cached, rather than recomputed on every evaluation.
newtype EvaluationContext = EvaluationContext
    { toMachineParameters :: Plutus.MachineParameters CekMachineCosts CekValue DefaultUni DefaultFun }

-- | Build the 'EvaluationContext'.
--
-- The input is a `Map` of strings to cost integer values (aka `Plutus.CostModelParams`, `Alonzo.CostModel`)
mkEvaluationContext :: Plutus.CostModelParams
                    -> Maybe EvaluationContext
mkEvaluationContext newCMP =
    EvaluationContext . Plutus.mkMachineParameters <$> Plutus.applyCostModelParams Plutus.defaultCekCostModel newCMP

-- | Comparably expensive to `mkEvaluationContext`, so it should only be used sparingly.
isCostModelParamsWellFormed :: Plutus.CostModelParams -> Bool
isCostModelParamsWellFormed = isJust . Plutus.applyCostModelParams Plutus.defaultCekCostModel

-- | The set of valid names that a cost model parameter can take for the specific protocol version.
-- It is used for the deserialization of `CostModelParams`.
costModelParamNames :: Set.Set Text.Text
costModelParamNames = Map.keysSet $ fromJust Plutus.defaultCostModelParams

-- | The raw cost model params, only to be used for testing purposes.
costModelParamsForTesting :: Plutus.CostModelParams
costModelParamsForTesting = fromJust Plutus.defaultCostModelParams

-- | only to be for testing purposes: make an evaluation context by applying an empty set of protocol parameters
evalCtxForTesting :: EvaluationContext
evalCtxForTesting = fromJust $ mkEvaluationContext mempty
