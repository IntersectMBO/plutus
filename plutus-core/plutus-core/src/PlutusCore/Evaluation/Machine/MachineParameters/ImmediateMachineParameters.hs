module PlutusCore.Evaluation.Machine.MachineParameters.ImmediateMachineParameters where

import PlutusCore.Builtin
import PlutusCore.Evaluation.Machine.CostModelInterface
import PlutusCore.Evaluation.Machine.MachineParameters.Default

import Control.Monad.Except
import GHC.Exts (inline)

immediateMachineParameters
    :: MonadError CostModelApplyError m => CostModelParams -> m DefaultMachineParameters
immediateMachineParameters = inline mkMachineParametersFor UnliftingImmediate
