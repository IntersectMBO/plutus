module Plutus.V1.Ledger.EvaluationContext
    ( EvaluationContext
    , mkEvaluationContext
    , CostModelParams
    , isCostModelParamsWellFormed
    , machineParametersImmediate
    , machineParametersDeferred
    , toMachineParameters
    , costModelParamNames
    ) where

import Plutus.ApiCommon
import PlutusCore as Plutus
import PlutusCore.Evaluation.Machine.BuiltinCostModel as Plutus
import PlutusCore.Evaluation.Machine.CostModelInterface as Plutus
import PlutusCore.Evaluation.Machine.MachineParameters as Plutus

import Barbies
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
              -- 'SerialiseData' builtin not available in V1
              paramSerialiseData = mempty
              -- TODO: do the same for schnorr and ellipticcurve costingfuns
            }
