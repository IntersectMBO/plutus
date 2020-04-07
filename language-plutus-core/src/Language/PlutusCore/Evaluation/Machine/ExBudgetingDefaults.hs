{-# LANGUAGE TemplateHaskell #-}
module Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults where

import           Data.Aeson.THReader
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting

defaultCostModel :: CostModel
defaultCostModel =
  $$(readJSONFromFile "language-plutus-core/src/costModel.json")
