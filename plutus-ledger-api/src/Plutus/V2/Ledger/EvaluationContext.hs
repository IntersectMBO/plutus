module Plutus.V2.Ledger.EvaluationContext
    ( module V1.EvaluationContext
    , costModelParamNames
    ) where

import Plutus.V1.Ledger.EvaluationContext as V1.EvaluationContext hiding (costModelParamNames)
import PlutusCore as Plutus (defaultCostModelParams)

import Data.Map qualified as Map
import Data.Maybe
import Data.Set qualified as Set
import Data.Text qualified as Text

-- | The set of valid names that a cost model parameter can take for this language version.
-- It is used for the deserialization of `CostModelParams`.
costModelParamNames :: Set.Set Text.Text
costModelParamNames = Map.keysSet $ fromJust Plutus.defaultCostModelParams

