-- | Defines the type of default machine parameters and a function for creating a value of the type.
-- We keep them separate, because the function unfolds into multiple thousands of lines of Core and
-- we want to instantiate it in two different ways on top of that, which gives another ton of Core
-- that we need to inspect, hence we dedicate an entire folder to that.
module PlutusCore.Evaluation.Machine.MachineParameters.Default where

import PlutusCore.Builtin
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.CostModelInterface
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Evaluation.Machine.MachineParameters
import UntypedPlutusCore.Evaluation.Machine.Cek

import Control.Monad.Except
import GHC.Exts (inline)

type DefaultMachineParameters = MachineParameters CekMachineCosts CekValue DefaultUni DefaultFun

mkMachineParametersFor :: (MonadError CostModelApplyError m)
                       => UnliftingMode
                       -> CostModelParams
                       -> m DefaultMachineParameters
mkMachineParametersFor unlMode newCMP =
    inline mkMachineParameters unlMode <$>
        applyCostModelParams defaultCekCostModel newCMP
{-# INLINE mkMachineParametersFor #-}
