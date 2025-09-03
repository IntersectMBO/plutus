-- editorconfig-checker-disable-file
-- | The API parameterized over some machine.

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module UntypedPlutusCore.Evaluation.Machine.CommonAPI
    (
    -- * Running the machine
    runCek
    , runCekDeBruijn
    , runCekNoEmit
    , evaluateCek
    , evaluateCekNoEmit
    , EvaluationResult(..)
    , splitStructuralOperational
    , unsafeSplitStructuralOperational
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
    , logWithCallTraceEmitter
    -- * Misc
    , CekValue(..)
    , readKnownCek
    , Hashable
    , ThrowableBuiltins
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
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.Name.Unique
import PlutusCore.Quote

import Control.Monad.Except
import Control.Monad.State
import Data.Text (Text)

-- The type of the machine (runner function).
type MachineRunner cost uni fun ann =
      MachineParameters CekMachineCosts fun (CekValue uni fun ann)
    -> ExBudgetMode cost uni fun
    -> EmitterMode uni fun
    -> NTerm uni fun ann
    -> CekReport cost NamedDeBruijn uni fun

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

{-| Evaluate a term using a machine with logging enabled and keep track of costing.
A wrapper around the internal runCek to debruijn input and undebruijn output.
*THIS FUNCTION IS PARTIAL if the input term contains free variables*
-}
runCek ::
      MachineRunner cost uni fun ann
    -> MachineParameters CekMachineCosts fun (CekValue uni fun ann)
    -> ExBudgetMode cost uni fun
    -> EmitterMode uni fun
    -> Term Name uni fun ann
    -> CekReport cost Name uni fun
runCek runner params mode emitMode term =
    -- translating input
    case runExcept @FreeVariableError $ deBruijnTerm term of
        Left fvError -> throw fvError
        Right dbt -> do
            -- Don't use 'let': https://github.com/IntersectMBO/plutus/issues/3876
            case runner params mode emitMode dbt of
                -- translating back the output
                CekReport res cost' logs ->
                    CekReport (mapTermCekResult gracefulUnDeBruijn res) cost' logs
  where
    -- *GRACEFULLY* undebruijnifies: a) the error-cause-term (if it exists) or b) the success
    -- *value-term.
    -- 'Graceful' means that the (a) && (b) undebruijnifications do not throw an error upon a free
    -- variable encounter: free debruijn indices will be turned to free, consistent uniques
    gracefulUnDeBruijn :: Term NamedDeBruijn uni fun () -> Term Name uni fun ()
    gracefulUnDeBruijn t = runQuote
                           . flip evalStateT mempty
                           $ unDeBruijnTermWith freeIndexAsConsistentLevel t

-- | Evaluate a term using a machine with logging disabled and keep track of costing.
-- *THIS FUNCTION IS PARTIAL if the input term contains free variables*
runCekNoEmit ::
      MachineRunner cost uni fun ann
    -> MachineParameters CekMachineCosts fun (CekValue uni fun ann)
    -> ExBudgetMode cost uni fun
    -> Term Name uni fun ann
    -> (Either (CekEvaluationException Name uni fun) (Term Name uni fun ()), cost)
runCekNoEmit runner params mode
    = -- throw away the logs
      (\(CekReport res cost _logs) -> (cekResultToEither res, cost))
    . runCek runner params mode noEmitter

-- | Evaluate a term using a machine with logging enabled.
-- *THIS FUNCTION IS PARTIAL if the input term contains free variables*
evaluateCek
    :: ThrowableBuiltins uni fun
    => MachineRunner RestrictingSt uni fun ann
    -> EmitterMode uni fun
    -> MachineParameters CekMachineCosts fun (CekValue uni fun ann)
    -> Term Name uni fun ann
    -> (Either (CekEvaluationException Name uni fun) (Term Name uni fun ()), [Text])
evaluateCek runner emitMode params
    = -- throw away the cost
      (\(CekReport res _cost logs) -> (cekResultToEither res, logs))
    . runCek runner params restrictingEnormous emitMode

-- | Evaluate a term using a machine with logging disabled.
-- *THIS FUNCTION IS PARTIAL if the input term contains free variables*
evaluateCekNoEmit
    :: ThrowableBuiltins uni fun
    => MachineRunner RestrictingSt uni fun ann
    -> MachineParameters CekMachineCosts fun (CekValue uni fun ann)
    -> Term Name uni fun ann
    -> Either (CekEvaluationException Name uni fun) (Term Name uni fun ())
evaluateCekNoEmit runner params = fst . runCekNoEmit runner params restrictingEnormous

-- | Unlift a value using a machine.
-- *THIS FUNCTION IS PARTIAL if the input term contains free variables*
readKnownCek
    :: (ThrowableBuiltins uni fun, ReadKnown (Term Name uni fun ()) a)
    => MachineRunner RestrictingSt uni fun ann
    -> MachineParameters CekMachineCosts fun (CekValue uni fun ann)
    -> Term Name uni fun ann
    -> Either (CekEvaluationException Name uni fun) a
readKnownCek runner params = evaluateCekNoEmit runner params >=> readKnownSelf
