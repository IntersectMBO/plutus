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
