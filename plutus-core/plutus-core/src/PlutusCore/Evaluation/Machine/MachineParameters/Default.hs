-- | Defines the type of default machine parameters and a function for creating a value of the type.
-- We keep them separate, because the function unfolds into multiple thousands of lines of Core that
-- we need to be able to visually inspect, hence we dedicate a separate file to it.
module PlutusCore.Evaluation.Machine.MachineParameters.Default where

import PlutusCore.Builtin
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.CostModelInterface
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Evaluation.Machine.MachineParameters
import UntypedPlutusCore.Evaluation.Machine.Cek

import Control.Monad.Except
import GHC.Exts (inline)

-- | 'MachineParameters' instantiated at CEK-machine-specific types and default builtins.
-- Encompasses everything we need for evaluating a UPLC program with default builtins using the CEK
-- machine.
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

-- | Produce a 'DefaultMachineParameters' given the version of the default set of built-in functions
-- and a 'CostModelParams', which gets applied on top of 'defaultCekCostModel'.
--
-- Whenever you need to evaluate UPLC in a performance-sensitive manner (e.g. in the production,
-- for benchmarking, for cost calibration etc), you MUST use this definition for creating a
-- 'DefaultMachineParameters' and not any other. Changing this definition in absolutely any way,
-- however trivial, requires running the benchmarks and making sure that the resulting GHC Core is
-- still sensible. E.g. you switch the order of arguments -- you run the benchmarks and check the
-- Core; you move this definition as-is to a different file -- you run the benchmarks and check the
-- Core; you change how it's exported (implicitly as a part of a whole-module export or explicitly
-- as a single definition) -- you get the idea.
--
-- This function is expensive, so its result needs to be cached if it's going to be used multiple
-- times.
mkMachineParametersFor
    :: MonadError CostModelApplyError m
    => BuiltinSemanticsVariant DefaultFun
    -> CostModelParams
    -> m DefaultMachineParameters
mkMachineParametersFor semvar newCMP =
    inline mkMachineParameters semvar <$>
        applyCostModelParams defaultCekCostModel newCMP
-- Not marking this function with @INLINE@, since at this point everything we wanted to be inlined
-- is inlined and there's zero reason to duplicate thousands and thousands of lines of Core down
-- the line.
