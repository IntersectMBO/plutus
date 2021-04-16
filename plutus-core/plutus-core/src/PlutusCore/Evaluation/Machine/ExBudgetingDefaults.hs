{-# LANGUAGE TemplateHaskell #-}
module PlutusCore.Evaluation.Machine.ExBudgetingDefaults where

import           Data.Aeson.THReader
import           PlutusCore.Evaluation.Machine.ExBudgeting

-- | The default cost model.
defaultCostModel :: CostModel
defaultCostModel =
  $$(readJSONFromFile "cost-model/data/costModel.json")

-- | The default cost model parameters.
defaultCostModelParams :: Maybe CostModelParams
defaultCostModelParams = extractModelParams defaultCostModel

-- Use this one when you've changed the type of `CostModel` and you can't load the json.
-- Then rerun
--  cabal run language-plutus-core-create-cost-model
-- import           Data.Default
-- defaultCostModel :: CostModel
-- defaultCostModel = def
