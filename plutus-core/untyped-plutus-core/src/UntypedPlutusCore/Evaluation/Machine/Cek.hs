-- | The API to the CEK machine.

{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module UntypedPlutusCore.Evaluation.Machine.Cek
    ( EvaluationResult(..)
    , CekValue(..)
    , CekUserError(..)
    , CekEvaluationException
    , CekBudgetSpender(..)
    , ErrorWithCause(..)
    , EvaluationError(..)
    , ExBudgetCategory(..)
    , CekExTally(..)
    , ExBudgetMode(..)
    , CountingSt (..)
    , TallyingSt (..)
    , RestrictingSt (..)
    , CekMachineCosts
    , Hashable
    , PrettyUni
    , counting
    , tallying
    , restricting
    , restrictingEnormous
    , extractEvaluationResult
    , runCek
    , runCekNoEmit
    , unsafeRunCekNoEmit
    , evaluateCek
    , evaluateCekNoEmit
    , unsafeEvaluateCek
    , unsafeEvaluateCekNoEmit
    , readKnownCek
    , enormousBudget
    , defaultCekMachineCosts
    , unitCekMachineCosts
    )
where

import           PlutusPrelude

import           UntypedPlutusCore.Core
import           UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts
import           UntypedPlutusCore.Evaluation.Machine.Cek.ExBudgetMode
import           UntypedPlutusCore.Evaluation.Machine.Cek.Internal

import           PlutusCore.Constant
import           PlutusCore.Evaluation.Machine.ExBudgetingDefaults        (defaultCekMachineCosts)
import           PlutusCore.Evaluation.Machine.ExMemory
import           PlutusCore.Evaluation.Machine.Exception
import           PlutusCore.Name
import           PlutusCore.Pretty
import           PlutusCore.Universe

import           Data.Ix

{- Note [CEK runners naming convention]
A function whose name ends in @NoEmit@ does not perform logging and so does not return any logs.
A function whose name starts with @unsafe@ throws exceptions instead of returning them purely.
A function from the @runCek@ family takes an 'ExBudgetMode' parameter and returns the final
'CekExBudgetState' (and possibly logs). Note that 'runCek' is defined in @...Cek.Internal@ for
reasons explained in Note [Compilation peculiarities].
A function from the @evaluateCek@ family does not return the final 'ExBudgetMode', nor does it
allow one to specify an 'ExBudgetMode'. I.e. such functions are only for fully evaluating programs
(and possibly returning logs). See also haddocks of 'enormousBudget'.
-}

-- | Evaluate a term using the CEK machine with logging disabled and keep track of costing.
runCekNoEmit
    :: ( uni `Everywhere` ExMemoryUsage, Ix fun, PrettyUni uni fun)
    => CekMachineCosts
    -> BuiltinsRuntime fun (CekValue uni fun)
    -> ExBudgetMode cost uni fun
    -> Term Name uni fun ()
    -> (Either (CekEvaluationException uni fun) (Term Name uni fun ()), cost)
runCekNoEmit cekcosts runtime mode term =
    case runCek cekcosts runtime mode False term of
        (errOrRes, cost', _) -> (errOrRes, cost')

-- | Unsafely evaluate a term using the CEK machine with logging disabled and keep track of costing.
-- May throw a 'CekMachineException'.
unsafeRunCekNoEmit
    :: ( GShow uni, Typeable uni
       , Closed uni, uni `EverywhereAll` '[ExMemoryUsage, PrettyConst]
       , Ix fun, Pretty fun, Typeable fun
       )
    => CekMachineCosts
    -> BuiltinsRuntime fun (CekValue uni fun)
    -> ExBudgetMode cost uni fun
    -> Term Name uni fun ()
    -> (EvaluationResult (Term Name uni fun ()), cost)
unsafeRunCekNoEmit cekcosts runtime mode =
    first unsafeExtractEvaluationResult . runCekNoEmit cekcosts runtime mode

-- | Evaluate a term using the CEK machine with logging enabled.
evaluateCek
    :: ( uni `Everywhere` ExMemoryUsage, Ix fun, PrettyUni uni fun)
    => CekMachineCosts
    -> BuiltinsRuntime fun (CekValue uni fun)
    -> Term Name uni fun ()
    -> (Either (CekEvaluationException uni fun) (Term Name uni fun ()), [String])
evaluateCek cekcosts runtime term =
    case runCek cekcosts runtime restrictingEnormous True term of
        (errOrRes, _, logs) -> (errOrRes, logs)

-- | Evaluate a term using the CEK machine with logging disabled.
evaluateCekNoEmit
    :: ( uni `Everywhere` ExMemoryUsage, Ix fun, PrettyUni uni fun)
    => CekMachineCosts
    -> BuiltinsRuntime fun (CekValue uni fun)
    -> Term Name uni fun ()
    -> Either (CekEvaluationException uni fun) (Term Name uni fun ())
evaluateCekNoEmit cekcosts runtime = fst . runCekNoEmit cekcosts runtime restrictingEnormous

-- | Evaluate a term using the CEK machine with logging enabled. May throw a 'CekMachineException'.
unsafeEvaluateCek
    :: ( GShow uni, Typeable uni
       , Closed uni, uni `EverywhereAll` '[ExMemoryUsage, PrettyConst]
       , Ix fun, Pretty fun, Typeable fun
       )
    => CekMachineCosts
    -> BuiltinsRuntime fun (CekValue uni fun)
    -> Term Name uni fun ()
    -> (EvaluationResult (Term Name uni fun ()), [String])
unsafeEvaluateCek cekcosts runtime = first unsafeExtractEvaluationResult . evaluateCek cekcosts runtime

-- | Evaluate a term using the CEK machine with logging disabled. May throw a 'CekMachineException'.
unsafeEvaluateCekNoEmit
    :: ( GShow uni, Typeable uni
       , Closed uni, uni `EverywhereAll` '[ExMemoryUsage, PrettyConst]
       , Ix fun, Pretty fun, Typeable fun
       )
    => CekMachineCosts
    -> BuiltinsRuntime fun (CekValue uni fun)
    -> Term Name uni fun ()
    -> EvaluationResult (Term Name uni fun ())
unsafeEvaluateCekNoEmit cekcosts runtime = unsafeExtractEvaluationResult . evaluateCekNoEmit cekcosts runtime

-- | Unlift a value using the CEK machine.
readKnownCek
    :: ( uni `Everywhere` ExMemoryUsage
       , KnownType (Term Name uni fun ()) a
       , Ix fun, PrettyUni uni fun
       )
    => CekMachineCosts
    -> BuiltinsRuntime fun (CekValue uni fun)
    -> Term Name uni fun ()
    -> Either (CekEvaluationException uni fun) a
readKnownCek cekcosts runtime = evaluateCekNoEmit cekcosts runtime >=> readKnown
