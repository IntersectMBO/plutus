{-# LANGUAGE TemplateHaskell #-}
module Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults where

import           Language.PlutusCore.Evaluation.Machine.ExBudgeting

-- import           Data.Aeson.THReader
-- defaultCostModel :: CostModel
-- defaultCostModel =
--   $$(readJSONFromFile "language-plutus-core/src/costModel.json")

-- Use this one when you've changed the type of `CostModel` and you can't load the json
import           Data.Default
defaultCostModel :: CostModel
defaultCostModel = def
