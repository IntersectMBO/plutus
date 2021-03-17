{-# LANGUAGE TemplateHaskell #-}
module PlutusCore.Evaluation.Machine.ExBudgetingDefaults where

import           Data.Aeson.THReader
import           PlutusCore.Evaluation.Machine.ExBudgeting

defaultCostModel :: CostModel
defaultCostModel =
  $$(readJSONFromFile "cost-model/data/costModel.json")

-- Use this one when you've changed the type of `CostModel` and you can't load the json.
-- Then rerun
--  cabal run language-plutus-core-create-cost-model
-- import           Data.Default
-- defaultCostModel :: CostModel
-- defaultCostModel = def
