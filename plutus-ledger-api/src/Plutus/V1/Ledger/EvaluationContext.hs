module Plutus.V1.Ledger.EvaluationContext
    ( EvaluationContext
    , mkEvaluationContext
    , CostModelParams
    , assertWellFormedCostModelParams
    , machineParametersImmediate
    , machineParametersDeferred
    , toMachineParameters
    , costModelParamNames
    , costModelParamsForTesting
    , evalCtxForTesting
    , CostModelApplyError (..)
    ) where

import Plutus.ApiCommon
import PlutusCore as Plutus
import PlutusCore.Evaluation.Machine.BuiltinCostModel as Plutus
import PlutusCore.Evaluation.Machine.CostModelInterface as Plutus
import PlutusCore.Evaluation.Machine.MachineParameters as Plutus

import Barbies
import Control.Exception
import Control.Lens
import Data.Map as Map
import Data.Maybe
import Data.Set as Set
import Data.Text qualified as Text

-- | The set of valid names that a cost model parameter can take for this language version.
-- It is used for the deserialization of `CostModelParams`.
costModelParamNames :: Set.Set Text.Text
costModelParamNames = Map.keysSet $ fromJust $ extractCostModelParams $
   defaultCekCostModel
   & builtinCostModel
   -- here we rely on 'Deriving.Aeson.OmitNothingFields'
   -- to skip jsonifying any fields which are cleared.
   %~ omitV2Builtins
  where
    -- "clears" some fields of builtincostmodel by setting them to Nothing. See 'MCostingFun'.
    omitV2Builtins :: BuiltinCostModel -> BuiltinCostModelBase MCostingFun
    omitV2Builtins bcm =
            -- transform all costing-functions to (Just costingFun)
            (bmap (MCostingFun . Just) bcm)
            {
              -- 'SerialiseData','EcdsaSecp256k1',SchnorrSecp256k1 builtins not available in V1
              paramSerialiseData = mempty
            , paramVerifyEcdsaSecp256k1Signature = mempty
            , paramVerifySchnorrSecp256k1Signature = mempty
            }

-- | The raw cost model params, only to be used for testing purposes.
costModelParamsForTesting :: Plutus.CostModelParams
costModelParamsForTesting = fromJust Plutus.defaultCostModelParams

-- | only to be for testing purposes: make an evaluation context by applying an empty set of protocol parameters
evalCtxForTesting :: EvaluationContext
evalCtxForTesting = either throw id $ mkEvaluationContext mempty
