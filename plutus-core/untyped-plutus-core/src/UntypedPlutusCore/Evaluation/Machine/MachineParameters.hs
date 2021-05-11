{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

module UntypedPlutusCore.Evaluation.Machine.MachineParameters
where

import           PlutusCore.Constant



import           PlutusCore
import           PlutusCore.Core.Type
import           PlutusCore.Evaluation.Machine.ExBudget                   ()
import           PlutusCore.Evaluation.Machine.ExBudgeting
import           PlutusCore.Evaluation.Machine.ExBudgetingDefaults
--import           PlutusCore.Evaluation.Machine.ExMemory

-- import           Data.Ix

import           UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts (CekMachineCosts, unitCekMachineCosts)
import           UntypedPlutusCore.Evaluation.Machine.Cek.Internal        (CekValue)

data CostModel machinecosts =
    CostModel {
      machineCostModel :: machinecosts
    , builtinCostModel :: BuiltinCostModel
    }

type CekCostModel = CostModel CekMachineCosts

defaultCekCostModel :: CostModel CekMachineCosts
defaultCekCostModel = CostModel defaultCekMachineCosts defaultBuiltinCostModel
--- defaultCekMachineCosts is CekMachineCosts

data MachineParameters machinecosts (val :: (* -> *) -> * -> *) uni fun =
    MachineParameters {
      machineCosts2   :: machinecosts
    , builtinsRuntime :: BuiltinsRuntime fun (val uni fun)
    }


toMachineParameters ::
    ( UniOf (val uni fun) ~ uni,
     CostingPart uni  fun ~ BuiltinCostModel
    , HasConstant (val uni fun)
    , ToBuiltinMeaning uni fun
    -- In Internal.hs we have `type instance UniOf (CekValue uni fun) = uni`, but we don't know that here

    )
    => CostModel machinecosts
    -> MachineParameters machinecosts val uni fun
toMachineParameters (CostModel machineCosts builtinCosts) =
    MachineParameters machineCosts (toBuiltinsRuntime builtinCosts)


p :: CekMachineCosts
p = machineCostModel defaultCekCostModel

defaultCekParameters :: MachineParameters CekMachineCosts CekValue DefaultUni DefaultFun
defaultCekParameters = toMachineParameters defaultCekCostModel

unitCekParameters :: MachineParameters CekMachineCosts CekValue DefaultUni DefaultFun
unitCekParameters = toMachineParameters (CostModel unitCekMachineCosts defaultBuiltinCostModel)
