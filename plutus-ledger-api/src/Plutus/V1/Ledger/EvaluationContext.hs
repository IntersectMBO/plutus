{-# LANGUAGE DeriveAnyClass #-}

-- GHC is asked to do quite a lot of optimization in this module, so we're increasing the amount of
-- ticks for the simplifier not to run out of them.
{-# OPTIONS_GHC -fsimpl-tick-factor=200 #-}

module Plutus.V1.Ledger.EvaluationContext
    ( EvaluationContext
    , mkEvaluationContext
    , CostModelParams
    , isCostModelParamsWellFormed
    , machineParametersImmediate
    , machineParametersDeferred
    , toMachineParameters
    , costModelParamNames
    , costModelParamsForTesting
    , evalCtxForTesting
    ) where

import PlutusCore as Plutus (DefaultFun, DefaultUni, UnliftingMode (..), defaultCekCostModel, defaultCostModelParams,
                             defaultUnliftingMode)
import PlutusCore.Evaluation.Machine.CostModelInterface as Plutus
import PlutusCore.Evaluation.Machine.MachineParameters as Plutus
import UntypedPlutusCore.Evaluation.Machine.Cek as Plutus

import Control.DeepSeq
import Data.Map as Map
import Data.Maybe
import Data.Set as Set
import Data.Text qualified as Text
import GHC.Exts (inline)
import GHC.Generics

type DefaultMachineParameters =
    Plutus.MachineParameters CekMachineCosts CekValue DefaultUni DefaultFun

-- | An opaque type that contains all the static parameters that the evaluator needs to evaluate a
-- script.  This is so that they can be computed once and cached, rather than recomputed on every
-- evaluation.
--
-- There are two sets of parameters: one is with immediate unlifting and the other one is with
-- deferred unlifting. We have to keep both of them, because depending on the language version
-- either one has to be used or the other. We also compile them separately due to all the inlining
-- and optimization that need to happen for things to be efficient.
data EvaluationContext = EvaluationContext
    { machineParametersImmediate :: DefaultMachineParameters
    , machineParametersDeferred  :: DefaultMachineParameters
    }
    deriving stock Generic
    deriving anyclass NFData

toMachineParameters :: EvaluationContext -> DefaultMachineParameters
toMachineParameters = case defaultUnliftingMode of
    UnliftingImmediate -> machineParametersImmediate
    UnliftingDeferred  -> machineParametersDeferred

{- Note [Inlining meanings of builtins]
It's vitally important to inline the 'toBuiltinMeaning' method of a set of built-in functions as
that allows GHC to look under lambdas and completely optimize multiple abstractions away.

There are two ways of doing that: by relying on 'INLINE' pragmas all the way up from the
'ToBuiltinMeaning' instance for the default set of builtins or by ensuring that 'toBuiltinsRuntime'
is compiled efficient by turning it into a one-method class (see
https://github.com/input-output-hk/plutus/pull/4419 for how that looks like). We chose the former,
because it's simpler. Although it's also less reliable: machine parameters are computed in
multiple places and we need to make sure that benchmarking, cost model calculations and the actual
production path have builtins compiled in the same way, 'cause otherwise performance analysis and
cost predictions can be wrong by a big margin without us knowing. Because of this danger in addition
to putting @INLINE@ pragmas on every relevant definition, we also stick a call to 'inline' at the
call site. We also do not attempt to only compile things efficiently where we need that and instead
inline the meanins of builtins everywhere. Just to be sure.

Note that a combination of @INLINABLE@ + 'inline' does not result in proper inlining for whatever
reason. It has to be @INLINE@ (and we add 'inline' on top of that for some additional reliability
as we did have cases where sticking 'inline' on something that already had @INLINE@ would fix
inlining).
-}

mkMachineParametersFor :: UnliftingMode -> Plutus.CostModelParams -> Maybe DefaultMachineParameters
mkMachineParametersFor unlMode newCMP =
    inline Plutus.mkMachineParameters unlMode <$>
        Plutus.applyCostModelParams Plutus.defaultCekCostModel newCMP
{-# INLINE mkMachineParametersFor #-}

-- See Note [Inlining meanings of builtins].
-- | Build the 'EvaluationContext'.
--
-- The input is a `Map` of strings to cost integer values (aka `Plutus.CostModelParams`, `Alonzo.CostModel`)
mkEvaluationContext :: Plutus.CostModelParams -> Maybe EvaluationContext
mkEvaluationContext newCMP =
    EvaluationContext
        <$> inline mkMachineParametersFor UnliftingImmediate newCMP
        <*> inline mkMachineParametersFor UnliftingDeferred newCMP

-- | Comparably expensive to `mkEvaluationContext`, so it should only be used sparingly.
isCostModelParamsWellFormed :: Plutus.CostModelParams -> Bool
isCostModelParamsWellFormed = isJust . Plutus.applyCostModelParams Plutus.defaultCekCostModel

-- | The set of valid names that a cost model parameter can take for the specific protocol version.
-- It is used for the deserialization of `CostModelParams`.
costModelParamNames :: Set.Set Text.Text
costModelParamNames = Map.keysSet $ fromJust Plutus.defaultCostModelParams

-- | The raw cost model params, only to be used for testing purposes.
costModelParamsForTesting :: Plutus.CostModelParams
costModelParamsForTesting = fromJust Plutus.defaultCostModelParams

-- | only to be for testing purposes: make an evaluation context by applying an empty set of protocol parameters
evalCtxForTesting :: EvaluationContext
evalCtxForTesting = fromJust $ mkEvaluationContext mempty
