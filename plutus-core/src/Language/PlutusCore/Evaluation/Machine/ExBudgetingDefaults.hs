{-# LANGUAGE TemplateHaskell #-}
module Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults where

import           Data.Aeson.THReader
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting

defaultCostModel :: CostModel
defaultCostModel =
  $$(readJSONFromFile "plutus-core/src/costModel.json")

-- Use this one when you've changed the type of `CostModel` and you can't load the json.
-- Then rerun
--  cabal run language-plutus-core-create-cost-model
-- import           Data.Default
-- defaultCostModel :: CostModel
-- defaultCostModel = def
