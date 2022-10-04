-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE StrictData        #-}
module PlutusLedgerApi.Internal.EvaluationContext
    ( EvaluationContext
    , mkDynEvaluationContext
    , toMachineParameters
    ) where

import PlutusLedgerApi.Common.Versions

import PlutusCore
import PlutusCore.Evaluation.Machine.MachineParameters.Default
import PlutusCore.Evaluation.Machine.MachineParameters.DeferredMachineParameters
import PlutusCore.Evaluation.Machine.MachineParameters.ImmediateMachineParameters
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.CostModelInterface as Plutus

import PlutusPrelude
import NoThunks.Class
import Control.Monad.Except

{-| An opaque type that contains all the static parameters that the evaluator needs to evaluate a
script.  This is so that they can be computed once and cached, rather than recomputed on every
evaluation.

There are two sets of parameters: one is with immediate unlifting and the other one is with
deferred unlifting. We have to keep both of them, because depending on the language version
 either one has to be used or the other. We also compile them separately due to all the inlining
 and optimization that need to happen for things to be efficient.
-}
data EvaluationContext = EvaluationContext
    { machineParametersImmediate :: DefaultMachineParameters
    , machineParametersDeferred  :: DefaultMachineParameters
    }
    deriving stock Generic
    deriving anyclass (NFData, NoThunks)

{-|  Build the 'EvaluationContext'.

The input is a `Map` of `Text`s to cost integer values (aka `Plutus.CostModelParams`, `Alonzo.CostModel`)
See Note [Inlining meanings of builtins].
-}
mkDynEvaluationContext :: MonadError CostModelApplyError m => BuiltinVersion DefaultFun -> Plutus.CostModelParams -> m EvaluationContext
mkDynEvaluationContext ver newCMP =
    EvaluationContext
        <$> immediateMachineParameters ver newCMP
        <*> deferredMachineParameters ver newCMP

toMachineParameters :: ProtocolVersion -> EvaluationContext -> DefaultMachineParameters
toMachineParameters pv = case unliftingModeIn pv of
    UnliftingImmediate -> machineParametersImmediate
    UnliftingDeferred  -> machineParametersDeferred

-- | Which unlifting mode should we use in the given 'ProtocolVersion'
-- so as to correctly construct the machine's parameters
unliftingModeIn :: ProtocolVersion -> UnliftingMode
unliftingModeIn pv =
    -- This just changes once in vasil hf version 7.0
    if pv >= VasilPV then UnliftingDeferred else UnliftingImmediate

