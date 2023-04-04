-- | The API to the Steppable CEK machine. Provides the same interface to original CEK machine.
{-# LANGUAGE TypeOperators #-}

module UntypedPlutusCore.Evaluation.Machine.SteppableCek
    (
    -- * Running the machine
    runCek
    , runCekDeBruijn
    , runCekNoEmit
    , unsafeRunCekNoEmit
    , evaluateCek
    , evaluateCekNoEmit
    , unsafeEvaluateCek
    , unsafeEvaluateCekNoEmit
    , EvaluationResult(..)
    , extractEvaluationResult
    , unsafeExtractEvaluationResult
    -- * Errors
    , CekUserError(..)
    , ErrorWithCause(..)
    , CekEvaluationException
    , EvaluationError(..)
    -- * Costing
    , ExBudgetCategory(..)
    , CekBudgetSpender(..)
    , ExBudgetMode(..)
    , StepKind(..)
    , CekExTally(..)
    , CountingSt (..)
    , TallyingSt (..)
    , RestrictingSt (..)
    , CekMachineCosts
    -- ** Costing modes
    , counting
    , tallying
    , restricting
    , restrictingEnormous
    , enormousBudget
    -- * Emitter modes
    , noEmitter
    , logEmitter
    , logWithTimeEmitter
    , logWithBudgetEmitter
    -- * Misc
    , CekValue(..)
    , readKnownCek
    , Hashable
    , PrettyUni
    )
where

import PlutusPrelude

import UntypedPlutusCore.Core
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts
import UntypedPlutusCore.Evaluation.Machine.Cek.EmitterMode
import UntypedPlutusCore.Evaluation.Machine.Cek.ExBudgetMode
import UntypedPlutusCore.Evaluation.Machine.CommonAPI qualified as Common
import UntypedPlutusCore.Evaluation.Machine.SteppableCek.Internal as S

import PlutusCore.Builtin
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.Name
import PlutusCore.Pretty

import Data.Text (Text)
import Universe

{-| Evaluate a term using the Steppable CEK machine with logging enabled and keep track of costing.
A wrapper around the internal runCek to debruijn input and undebruijn output.
*THIS FUNCTION IS PARTIAL if the input term contains free variables*
-}
runCek
    :: PrettyUni uni fun
    => MachineParameters CekMachineCosts fun (CekValue uni fun ann)
    -> ExBudgetMode cost uni fun
    -> EmitterMode uni fun
    -> Term Name uni fun ann
    -> (Either (CekEvaluationException Name uni fun) (Term Name uni fun ()), cost, [Text])
runCek = Common.runCek S.runCekDeBruijn

-- | Evaluate a term using the Steppable CEK machine with logging disabled and
-- keep track of costing.
-- *THIS FUNCTION IS PARTIAL if the input term contains free variables*
runCekNoEmit
    :: PrettyUni uni fun
    => MachineParameters CekMachineCosts fun (CekValue uni fun ann)
    -> ExBudgetMode cost uni fun
    -> Term Name uni fun ann
    -> (Either (CekEvaluationException Name uni fun) (Term Name uni fun ()), cost)
runCekNoEmit = Common.runCekNoEmit S.runCekDeBruijn

{-| Unsafely evaluate a term using the Steppable CEK machine with logging disabled
-- and keep track of costing.
May throw a 'CekMachineException'.
*THIS FUNCTION IS PARTIAL if the input term contains free variables*
-}
unsafeRunCekNoEmit
    :: ( Pretty (SomeTypeIn uni), Typeable uni
       , Closed uni, uni `Everywhere` PrettyConst
       , Pretty fun, Typeable fun
       )
    => MachineParameters CekMachineCosts fun (CekValue uni fun ann)
    -> ExBudgetMode cost uni fun
    -> Term Name uni fun ann
    -> (EvaluationResult (Term Name uni fun ()), cost)
unsafeRunCekNoEmit = Common.unsafeRunCekNoEmit S.runCekDeBruijn

-- | Evaluate a term using the Steppable CEK machine with logging enabled.
-- *THIS FUNCTION IS PARTIAL if the input term contains free variables*
evaluateCek
    :: PrettyUni uni fun
    => EmitterMode uni fun
    -> MachineParameters CekMachineCosts fun (CekValue uni fun ann)
    -> Term Name uni fun ann
    -> (Either (CekEvaluationException Name uni fun) (Term Name uni fun ()), [Text])
evaluateCek = Common.evaluateCek S.runCekDeBruijn

-- | Evaluate a term using the Steppable CEK machine with logging disabled.
-- *THIS FUNCTION IS PARTIAL if the input term contains free variables*
evaluateCekNoEmit
    :: PrettyUni uni fun
    => MachineParameters CekMachineCosts fun (CekValue uni fun ann)
    -> Term Name uni fun ann
    -> Either (CekEvaluationException Name uni fun) (Term Name uni fun ())
evaluateCekNoEmit = Common.evaluateCekNoEmit S.runCekDeBruijn

-- | Evaluate a term using the Steppable CEK machine with logging enabled.
-- May throw a 'CekMachineException'.
-- *THIS FUNCTION IS PARTIAL if the input term contains free variables*
unsafeEvaluateCek
    :: ( Pretty (SomeTypeIn uni), Typeable uni
       , Closed uni, uni `Everywhere` PrettyConst
       , Pretty fun, Typeable fun
       )
    => EmitterMode uni fun
    -> MachineParameters CekMachineCosts fun (CekValue uni fun ann)
    -> Term Name uni fun ann
    -> (EvaluationResult (Term Name uni fun ()), [Text])
unsafeEvaluateCek = Common.unsafeEvaluateCek S.runCekDeBruijn

-- | Evaluate a term using the Steppable CEK machine with logging disabled.
-- May throw a 'CekMachineException'.
-- *THIS FUNCTION IS PARTIAL if the input term contains free variables*
unsafeEvaluateCekNoEmit
    :: ( Pretty (SomeTypeIn uni), Typeable uni
       , Closed uni, uni `Everywhere` PrettyConst
       , Pretty fun, Typeable fun
       )
    => MachineParameters CekMachineCosts fun (CekValue uni fun ann)
    -> Term Name uni fun ann
    -> EvaluationResult (Term Name uni fun ())
unsafeEvaluateCekNoEmit = Common.unsafeEvaluateCekNoEmit S.runCekDeBruijn

-- | Unlift a value using the Steppable CEK machine.
-- *THIS FUNCTION IS PARTIAL if the input term contains free variables*
readKnownCek
    :: ( ReadKnown (Term Name uni fun ()) a
       , PrettyUni uni fun
       )
    => MachineParameters CekMachineCosts fun (CekValue uni fun ann)
    -> Term Name uni fun ann
    -> Either (CekEvaluationException Name uni fun) a
readKnownCek = Common.readKnownCek S.runCekDeBruijn
