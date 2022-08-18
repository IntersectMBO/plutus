-- Keep this module in sync with @DeferredMachineParameters.hs@

-- GHC worker-wrapper-transforms the denotation of a builtin without this flag, which only
-- introduces a redundant indirection. There doesn't seem to be any performance difference, but the
-- Core is tidier when the worker-wrapper optimization does not happen.
{-# OPTIONS_GHC -fno-worker-wrapper #-}

-- | This module provides a 'DefaultMachineParameters' with builtins doing immediate unlifting (see
-- the docs of 'UnliftingMode' for more info). We keep it separate, because we want to be able to
-- inspect the Core that it compiles to and it's already multiple thousands lines of code, so
-- keeping it together with other stuff would make it even harder to read that Core.
module PlutusCore.Evaluation.Machine.MachineParameters.ImmediateMachineParameters where

import PlutusCore.Builtin
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.CostModelInterface
import PlutusCore.Evaluation.Machine.MachineParameters.Default

import Control.Monad.Except
import GHC.Exts (inline)

-- | Get a 'DefaultMachineParameters' with builtins doing immediate unlifting.
immediateMachineParameters
    :: MonadError CostModelApplyError m
    => BuiltinVersion DefaultFun
    -> CostModelParams -> m DefaultMachineParameters
immediateMachineParameters ver = inline mkMachineParametersFor ver UnliftingImmediate
-- No need to mark this as 'INLINE', since a 'CostModelParams' comes in at runtime and so we can't
-- get the builtins to optimize any further. We don't need to optimize the 'MonadError' part, since
-- it's only computed when the parameters change, not multiple times (not even once) per contract
-- like builtins.
