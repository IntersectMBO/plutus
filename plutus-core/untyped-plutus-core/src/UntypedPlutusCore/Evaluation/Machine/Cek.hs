{-# LANGUAGE TypeOperators #-}

-- | The API to the CEK machine.
module UntypedPlutusCore.Evaluation.Machine.Cek
  ( -- * Running the machine
    runCek
  , runCekDeBruijn
  , runCekNoEmit
  , evaluateCek
  , evaluateCekNoEmit
  , EvaluationResult (..)
  , splitStructuralOperational
  , unsafeSplitStructuralOperational

    -- * Errors
  , CekUserError (..)
  , ErrorWithCause (..)
  , CekEvaluationException
  , EvaluationError (..)

    -- * Costing
  , ExBudgetCategory (..)
  , CekBudgetSpender (..)
  , ExBudgetMode (..)
  , StepKind (..)
  , CekExTally (..)
  , CountingSt (..)
  , TallyingSt (..)
  , RestrictingSt (..)
  , CekMachineCosts

    -- ** Costing modes
  , monoidalBudgeting
  , counting
  , tallying
  , restricting
  , restrictingLarge
  , restrictingEnormous
  , enormousBudget

    -- * Emitter modes
  , noEmitter
  , logEmitter
  , logWithTimeEmitter
  , logWithBudgetEmitter
  , logWithCallTraceEmitter

    -- * Misc
  , BuiltinsRuntime (..)
  , CekResult (..)
  , CekReport (..)
  , cekResultToEither
  , CekValue (..)
  , DischargeResult (..)
  , dischargeResultToTerm
  , readKnownCek
  , Hashable
  , ThrowableBuiltins
  )
where

import UntypedPlutusCore.Core
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts
import UntypedPlutusCore.Evaluation.Machine.Cek.EmitterMode
import UntypedPlutusCore.Evaluation.Machine.Cek.ExBudgetMode
import UntypedPlutusCore.Evaluation.Machine.Cek.Internal
import UntypedPlutusCore.Evaluation.Machine.CommonAPI qualified as Common

import PlutusCore.Builtin
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.Name.Unique

import Data.Text (Text)

{-| Evaluate a term using the CEK machine with logging enabled and keep track of costing.
A wrapper around the internal runCek to debruijn input and undebruijn output.
*THIS FUNCTION IS PARTIAL if the input term contains free variables* -}
runCek
  :: ThrowableBuiltins uni fun
  => MachineParameters CekMachineCosts fun (CekValue uni fun ann)
  -> ExBudgetMode cost uni fun
  -> EmitterMode uni fun
  -> Term Name uni fun ann
  -> CekReport cost Name uni fun
runCek = Common.runCek runCekDeBruijn

{-| Evaluate a term using the CEK machine with logging disabled and keep track of costing.
*THIS FUNCTION IS PARTIAL if the input term contains free variables* -}
runCekNoEmit
  :: ThrowableBuiltins uni fun
  => MachineParameters CekMachineCosts fun (CekValue uni fun ann)
  -> ExBudgetMode cost uni fun
  -> Term Name uni fun ann
  -> (Either (CekEvaluationException Name uni fun) (Term Name uni fun ()), cost)
runCekNoEmit = Common.runCekNoEmit runCekDeBruijn

{-| Evaluate a term using the CEK machine with logging enabled.
*THIS FUNCTION IS PARTIAL if the input term contains free variables* -}
evaluateCek
  :: ThrowableBuiltins uni fun
  => EmitterMode uni fun
  -> MachineParameters CekMachineCosts fun (CekValue uni fun ann)
  -> Term Name uni fun ann
  -> (Either (CekEvaluationException Name uni fun) (Term Name uni fun ()), [Text])
evaluateCek = Common.evaluateCek runCekDeBruijn

{-| Evaluate a term using the CEK machine with logging disabled.
*THIS FUNCTION IS PARTIAL if the input term contains free variables* -}
evaluateCekNoEmit
  :: ThrowableBuiltins uni fun
  => MachineParameters CekMachineCosts fun (CekValue uni fun ann)
  -> Term Name uni fun ann
  -> Either (CekEvaluationException Name uni fun) (Term Name uni fun ())
evaluateCekNoEmit = Common.evaluateCekNoEmit runCekDeBruijn

{-| Unlift a value using the CEK machine.
*THIS FUNCTION IS PARTIAL if the input term contains free variables* -}
readKnownCek
  :: (ThrowableBuiltins uni fun, ReadKnown (Term Name uni fun ()) a)
  => MachineParameters CekMachineCosts fun (CekValue uni fun ann)
  -> Term Name uni fun ann
  -> Either (CekEvaluationException Name uni fun) a
readKnownCek = Common.readKnownCek runCekDeBruijn
