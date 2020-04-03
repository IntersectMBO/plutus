{-# LANGUAGE TemplateHaskell #-}
module Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults where

import Language.PlutusCore.Evaluation.Machine.ExBudgeting
import Data.Aeson.THReader

defaultCostingFunParameters :: CostingFunParameters
defaultCostingFunParameters =
  $$(readJSONFromFile "src/costingFunctionParameters.json")