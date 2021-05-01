{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

module PlutusCore.Evaluation.Machine.ExBudgetingDefaults where

import           Data.Aeson.THReader
import           PlutusCore.Evaluation.Machine.ExBudget    ()
import           PlutusCore.Evaluation.Machine.ExBudgeting
import           PlutusCore.Evaluation.Machine.ExMemory    ()

import           UntypedPlutusCore.Evaluation.Machine.Cek  (CekCosts)


-- | The default cost model for built-in functions.
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

-- | Default costs for CEK machine instructions.
defaultCekCosts :: CekCosts
defaultCekCosts =
  $$(readJSONFromFile "cost-model/data/cekCosts.json")

