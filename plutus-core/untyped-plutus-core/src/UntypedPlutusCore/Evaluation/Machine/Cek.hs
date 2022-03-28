-- | The API to the CEK machine.

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module UntypedPlutusCore.Evaluation.Machine.Cek
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
import UntypedPlutusCore.DeBruijn
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts
import UntypedPlutusCore.Evaluation.Machine.Cek.EmitterMode
import UntypedPlutusCore.Evaluation.Machine.Cek.ExBudgetMode
import UntypedPlutusCore.Evaluation.Machine.Cek.Internal

import PlutusCore.Builtin
import PlutusCore.Evaluation.Machine.ExMemory
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.Name
import PlutusCore.Pretty
import PlutusCore.Quote

import Control.Monad.Except
import Control.Monad.State
import Data.Bifunctor
import Data.Ix (Ix)
import Data.Text (Text)
import Universe

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

{-| Evaluate a term using the CEK machine with logging enabled and keep track of costing.
A wrapper around the internal runCek to debruijn input and undebruijn output.
*THIS FUNCTION IS PARTIAL if the input term contains free variables*
-}
runCek
    :: (uni `Everywhere` ExMemoryUsage, Ix fun, PrettyUni uni fun)
    => MachineParameters CekMachineCosts CekValue uni fun
    -> ExBudgetMode cost uni fun
    -> EmitterMode uni fun
    -> Term Name uni fun ()
    -> (Either (CekEvaluationException Name uni fun) (Term Name uni fun ()), cost, [Text])
runCek params mode emitMode term =
    -- translating input
    case runExcept @FreeVariableError $ deBruijnTerm term of
        Left fvError -> throw fvError
        Right dbt -> do
            -- Don't use 'let': https://github.com/input-output-hk/plutus/issues/3876
            case runCekDeBruijn params mode emitMode dbt of
                -- translating back the output
                (res, cost', logs) -> (unDeBruijnResult res, cost', logs)
  where
    -- *GRACEFULLY* undebruijnifies: a) the error-cause-term (if it exists) or b) the success value-term.
    -- 'Graceful' means that the (a) && (b) undebruijnifications do not throw an error upon a free variable encounter.
    unDeBruijnResult :: Either (CekEvaluationException NamedDeBruijn uni fun) (Term NamedDeBruijn uni fun ())
                     -> Either (CekEvaluationException Name uni fun) (Term Name uni fun ())
    unDeBruijnResult = bimap (fmap gracefulUnDeBruijn) gracefulUnDeBruijn

    -- free debruijn indices will be turned to free, consistent uniques
    gracefulUnDeBruijn :: Term NamedDeBruijn uni fun () -> Term Name uni fun ()
    gracefulUnDeBruijn t = runQuote
                           . flip evalStateT mempty
                           $ unDeBruijnTermWith freeIndexAsConsistentLevel t

-- | Evaluate a term using the CEK machine with logging disabled and keep track of costing.
-- *THIS FUNCTION IS PARTIAL if the input term contains free variables*
runCekNoEmit
    :: (uni `Everywhere` ExMemoryUsage, Ix fun, PrettyUni uni fun)
    => MachineParameters CekMachineCosts CekValue uni fun
    -> ExBudgetMode cost uni fun
    -> Term Name uni fun ()
    -> (Either (CekEvaluationException Name uni fun) (Term Name uni fun ()), cost)
runCekNoEmit params mode =
    -- throw away the logs
    (\(res, cost, _logs) -> (res, cost)) . runCek params mode noEmitter

{-| Unsafely evaluate a term using the CEK machine with logging disabled and keep track of costing.
May throw a 'CekMachineException'.
*THIS FUNCTION IS PARTIAL if the input term contains free variables*
-}
unsafeRunCekNoEmit
    :: ( GShow uni, Typeable uni
       , Closed uni, uni `EverywhereAll` '[ExMemoryUsage, PrettyConst]
       , Ix fun, Pretty fun, Typeable fun
       )
    => MachineParameters CekMachineCosts CekValue uni fun
    -> ExBudgetMode cost uni fun
    -> Term Name uni fun ()
    -> (EvaluationResult (Term Name uni fun ()), cost)
unsafeRunCekNoEmit params mode =
    -- Don't use 'first': https://github.com/input-output-hk/plutus/issues/3876
    (\(e, l) -> (unsafeExtractEvaluationResult e, l)) . runCekNoEmit params mode

-- | Evaluate a term using the CEK machine with logging enabled.
-- *THIS FUNCTION IS PARTIAL if the input term contains free variables*
evaluateCek
    :: ( uni `Everywhere` ExMemoryUsage, Ix fun, PrettyUni uni fun)
    => EmitterMode uni fun
    -> MachineParameters CekMachineCosts CekValue uni fun
    -> Term Name uni fun ()
    -> (Either (CekEvaluationException Name uni fun) (Term Name uni fun ()), [Text])
evaluateCek emitMode params =
    -- throw away the cost
    (\(res, _cost, logs) -> (res, logs)) . runCek params restrictingEnormous emitMode

-- | Evaluate a term using the CEK machine with logging disabled.
-- *THIS FUNCTION IS PARTIAL if the input term contains free variables*
evaluateCekNoEmit
    :: ( uni `Everywhere` ExMemoryUsage, Ix fun, PrettyUni uni fun)
    => MachineParameters CekMachineCosts CekValue uni fun
    -> Term Name uni fun ()
    -> Either (CekEvaluationException Name uni fun) (Term Name uni fun ())
evaluateCekNoEmit params = fst . runCekNoEmit params restrictingEnormous

-- | Evaluate a term using the CEK machine with logging enabled. May throw a 'CekMachineException'.
-- *THIS FUNCTION IS PARTIAL if the input term contains free variables*
unsafeEvaluateCek
    :: ( GShow uni, Typeable uni
       , Closed uni, uni `EverywhereAll` '[ExMemoryUsage, PrettyConst]
       , Ix fun, Pretty fun, Typeable fun
       )
    => EmitterMode uni fun
    -> MachineParameters CekMachineCosts CekValue uni fun
    -> Term Name uni fun ()
    -> (EvaluationResult (Term Name uni fun ()), [Text])
unsafeEvaluateCek emitTime params =
    -- Don't use 'first': https://github.com/input-output-hk/plutus/issues/3876
    (\(e, l) -> (unsafeExtractEvaluationResult e, l)) . evaluateCek emitTime params

-- | Evaluate a term using the CEK machine with logging disabled. May throw a 'CekMachineException'.
-- *THIS FUNCTION IS PARTIAL if the input term contains free variables*
unsafeEvaluateCekNoEmit
    :: ( GShow uni, Typeable uni
       , Closed uni, uni `EverywhereAll` '[ExMemoryUsage, PrettyConst]
       , Ix fun, Pretty fun, Typeable fun
       )
    => MachineParameters CekMachineCosts CekValue uni fun
    -> Term Name uni fun ()
    -> EvaluationResult (Term Name uni fun ())
unsafeEvaluateCekNoEmit params = unsafeExtractEvaluationResult . evaluateCekNoEmit params

-- | Unlift a value using the CEK machine.
-- *THIS FUNCTION IS PARTIAL if the input term contains free variables*
readKnownCek
    :: ( uni `Everywhere` ExMemoryUsage
       , ReadKnown (Term Name uni fun ()) a
       , Ix fun, PrettyUni uni fun
       )
    => MachineParameters CekMachineCosts CekValue uni fun
    -> Term Name uni fun ()
    -> Either (CekEvaluationException Name uni fun) a
readKnownCek params = evaluateCekNoEmit params >=> readKnownSelf
