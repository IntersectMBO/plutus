-- | The API to the CEK machine.

{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE RankNTypes    #-}
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
    , Hashable
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
    )
where

import           PlutusPrelude

import           UntypedPlutusCore.Core
import           UntypedPlutusCore.Evaluation.Machine.Cek.ExBudgetMode
import           UntypedPlutusCore.Evaluation.Machine.Cek.Internal

import           PlutusCore.Constant
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
    :: ( Closed uni, uni `Everywhere` ExMemoryUsage
       , Ix fun, ExMemoryUsage fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> ExBudgetMode cost uni fun
    -> Term Name uni fun ()
    -> (Either (CekEvaluationException uni fun) (Term Name uni fun ()), cost)
runCekNoEmit runtime mode term =
    case runCek runtime mode False term of
        (errOrRes, cost', _) -> (errOrRes, cost')

-- | Unsafely evaluate a term using the CEK machine with logging disabled and keep track of costing.
-- May throw a 'CekMachineException'.
unsafeRunCekNoEmit
    :: ( GShow uni, Typeable uni
       , Closed uni, uni `EverywhereAll` '[ExMemoryUsage, PrettyConst]
       , Ix fun, Pretty fun, Typeable fun, ExMemoryUsage fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> ExBudgetMode cost uni fun
    -> Term Name uni fun ()
    -> (EvaluationResult (Term Name uni fun ()), cost)
unsafeRunCekNoEmit runtime mode =
    first unsafeExtractEvaluationResult . runCekNoEmit runtime mode

-- | Evaluate a term using the CEK machine with logging enabled.
evaluateCek
    :: ( Closed uni, uni `Everywhere` ExMemoryUsage
       , Ix fun, ExMemoryUsage fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> Term Name uni fun ()
    -> (Either (CekEvaluationException uni fun) (Term Name uni fun ()), [String])
evaluateCek runtime term =
    case runCek runtime restrictingEnormous True term of
        (errOrRes, _, logs) -> (errOrRes, logs)

-- | Evaluate a term using the CEK machine with logging disabled.
evaluateCekNoEmit
    :: ( Closed uni, uni `Everywhere` ExMemoryUsage
       , Ix fun, ExMemoryUsage fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> Term Name uni fun ()
    -> Either (CekEvaluationException uni fun) (Term Name uni fun ())
evaluateCekNoEmit runtime = fst . runCekNoEmit runtime restrictingEnormous

-- | Evaluate a term using the CEK machine with logging enabled. May throw a 'CekMachineException'.
unsafeEvaluateCek
    :: ( GShow uni, Typeable uni
       , Closed uni, uni `EverywhereAll` '[ExMemoryUsage, PrettyConst]
       , Ix fun, Pretty fun, Typeable fun, ExMemoryUsage fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> Term Name uni fun ()
    -> (EvaluationResult (Term Name uni fun ()), [String])
unsafeEvaluateCek runtime = first unsafeExtractEvaluationResult . evaluateCek runtime

-- | Evaluate a term using the CEK machine with logging disabled. May throw a 'CekMachineException'.
unsafeEvaluateCekNoEmit
    :: ( GShow uni, Typeable uni
       , Closed uni, uni `EverywhereAll` '[ExMemoryUsage, PrettyConst]
       , Ix fun, Pretty fun, Typeable fun, ExMemoryUsage fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> Term Name uni fun ()
    -> EvaluationResult (Term Name uni fun ())
unsafeEvaluateCekNoEmit runtime = unsafeExtractEvaluationResult . evaluateCekNoEmit runtime

-- | Unlift a value using the CEK machine.
readKnownCek
    :: ( Closed uni, uni `Everywhere` ExMemoryUsage
       , KnownType (Term Name uni fun ()) a
       , Ix fun, ExMemoryUsage fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> Term Name uni fun ()
    -> Either (CekEvaluationException uni fun) a
readKnownCek runtime = evaluateCekNoEmit runtime >=> readKnown
