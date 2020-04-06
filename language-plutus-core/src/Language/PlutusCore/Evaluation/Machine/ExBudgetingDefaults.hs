{-# LANGUAGE TemplateHaskell #-}
module Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults where

import Language.PlutusCore.Evaluation.Machine.ExBudgeting
import Data.Aeson.THReader

defaultCostModel :: CostModel
defaultCostModel =
  $$(readJSONFromFile "language-plutus-core/src/costModel.json")