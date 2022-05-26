module PlutusCore.Evaluation.Machine.MachineParameters.DeferredMachineParameters where

import PlutusCore.Builtin
import PlutusCore.Evaluation.Machine.CostModelInterface
import PlutusCore.Evaluation.Machine.MachineParameters.Default

import Control.Monad.Except
import GHC.Exts (inline)

deferredMachineParameters
    :: MonadError CostModelApplyError m => CostModelParams -> m DefaultMachineParameters
deferredMachineParameters = inline mkMachineParametersFor UnliftingDeferred
