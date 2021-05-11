{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

module PlutusCore.Evaluation.Machine.ExBudgetingDefaults where

import           Data.Aeson.THReader
import           PlutusCore.Evaluation.Machine.ExBudget                   ()
import           PlutusCore.Evaluation.Machine.ExBudgeting
import           PlutusCore.Evaluation.Machine.ExMemory                   ()

import           UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts (CekMachineCosts)


-- | The default cost model for built-in functions.
defaultBuiltinCostModel :: BuiltinCostModel
defaultBuiltinCostModel =
  $$(readJSONFromFile "cost-model/data/builtinCostModel.json")

-- | The default cost model parameters.
defaultBuiltinCostModelParams :: Maybe BuiltinCostModelParams
defaultBuiltinCostModelParams = extractBuiltinCostModelParams defaultBuiltinCostModel

-- Use this one when you've changed the type of `CostModel` and you can't load the json.
-- Then rerun
--  cabal run language-plutus-core-create-cost-model
-- import           Data.Default
-- defaultBuiltinCostModel :: BuiltinCostModel
-- defaultBuiltinCostModel = def

-- | Default costs for CEK machine instructions.
defaultCekMachineCosts :: CekMachineCosts
defaultCekMachineCosts =
  $$(readJSONFromFile "cost-model/data/cekMachineCosts.json")

