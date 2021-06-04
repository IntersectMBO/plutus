{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}

module PlutusCore.Evaluation.Machine.ExBudgetingDefaults
    ( defaultBuiltinsRuntime
    , defaultCekCostModel
    , unitCekCostModel
    , defaultCekMachineCosts
    , defaultCostModelParams
    , defaultBuiltinCostModel
    )

where

import           Data.Aeson.THReader

import           PlutusCore.Constant

import           PlutusCore.Default
import           PlutusCore.Evaluation.Machine.BuiltinCostModel
import           PlutusCore.Evaluation.Machine.CostModelInterface
import           PlutusCore.Evaluation.Machine.ExBudget                   ()
import           PlutusCore.Evaluation.Machine.ExMemory                   ()
import           PlutusCore.Evaluation.Machine.MachineParameters

import           UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts


-- | The default cost model for built-in functions.
defaultBuiltinCostModel :: BuiltinCostModel
defaultBuiltinCostModel =
  $$(readJSONFromFile "cost-model/data/builtinCostModel.json")

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

defaultCekCostModel :: CostModel CekMachineCosts BuiltinCostModel
defaultCekCostModel = CostModel defaultCekMachineCosts defaultBuiltinCostModel
--- defaultCekMachineCosts is CekMachineCosts

unitCekCostModel :: CostModel CekMachineCosts BuiltinCostModel
unitCekCostModel = CostModel unitCekMachineCosts defaultBuiltinCostModel

-- | The default cost model data.  This is exposed to the ledger, so let's not
-- confuse anybody by mentioning the CEK machine
defaultCostModelParams :: Maybe CostModelParams
defaultCostModelParams = extractCostModelParams defaultCekCostModel

defaultBuiltinsRuntime :: HasConstantIn DefaultUni term => BuiltinsRuntime DefaultFun term
defaultBuiltinsRuntime = toBuiltinsRuntime defaultBuiltinCostModel
