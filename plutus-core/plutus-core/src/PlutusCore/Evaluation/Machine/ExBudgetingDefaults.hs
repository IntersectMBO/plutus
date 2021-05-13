{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}

module PlutusCore.Evaluation.Machine.ExBudgetingDefaults where

import           Data.Aeson.THReader

import           PlutusCore
import           PlutusCore.Constant

import           PlutusCore.Evaluation.Machine.BuiltinCostModel
import           PlutusCore.Evaluation.Machine.CostModelInterface
import           PlutusCore.Evaluation.Machine.ExBudget                   ()
import           PlutusCore.Evaluation.Machine.ExMemory                   ()
import           PlutusCore.Evaluation.Machine.MachineParameters

import           UntypedPlutusCore.Evaluation.Machine.Cek
import           UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts (unitCekMachineCosts)


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

defaultCekCostModel :: CostModel CekMachineCosts
defaultCekCostModel = CostModel defaultCekMachineCosts defaultBuiltinCostModel
--- defaultCekMachineCosts is CekMachineCosts

-- | The default cost model data.
defaultCekCostModelData :: Maybe CostModelData
defaultCekCostModelData = extractCostModelData defaultCekCostModel

defaultCekParameters :: MachineParameters CekMachineCosts CekValue DefaultUni DefaultFun
defaultCekParameters = toMachineParameters defaultCekCostModel

unitCekParameters :: MachineParameters CekMachineCosts CekValue DefaultUni DefaultFun
unitCekParameters = toMachineParameters (CostModel unitCekMachineCosts defaultBuiltinCostModel)

defaultBuiltinsRuntime :: HasConstantIn DefaultUni term => BuiltinsRuntime DefaultFun term
defaultBuiltinsRuntime = toBuiltinsRuntime defaultBuiltinCostModel

