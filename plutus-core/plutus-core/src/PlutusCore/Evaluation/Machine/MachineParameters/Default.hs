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

type DefaultMachineParameters =
    MachineParameters CekMachineCosts DefaultFun (CekValue DefaultUni DefaultFun ())

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
inline the meanings of builtins everywhere. Just to be sure.

Note that a combination of @INLINABLE@ + 'inline' does not result in proper inlining for whatever
reason. It has to be @INLINE@ (and we add 'inline' on top of that for some additional reliability
as we did have cases where sticking 'inline' on something that already had @INLINE@ would fix
inlining).
-}

mkMachineParametersFor
    :: (MonadError CostModelApplyError m)
    => BuiltinSemanticsVariant DefaultFun
    -> CostModelParams
    -> m DefaultMachineParameters
mkMachineParametersFor semvar newCMP =
    inline mkMachineParameters semvar <$>
        applyCostModelParams defaultCekCostModel newCMP
-- Not marking this function with @INLINE@, since at this point everything we wanted to be inlined
-- is inlined and there's zero reason to duplicate thousands and thousands of lines of Core down
-- the line.
