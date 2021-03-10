-- | The CEK machine.
-- The CEK machine relies on variables having non-equal 'Unique's whenever they have non-equal
-- string names. I.e. 'Unique's are used instead of string names. This is for efficiency reasons.
-- The CEK machines handles name capture by design.

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NPlusKPatterns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.UntypedPlutusCore.Evaluation.Machine.Cek
    ( EvaluationResult(..)
    , CekValue(..)
    , CekUserError(..)
    , CekEvaluationException
    , BudgetSpender(..)
    , ErrorWithCause(..)
    , EvaluationError(..)
    , ExBudgetCategory(..)
    , CekExTally
    , ExBudgetMode
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
    )
where

import           ErrorCode
import           PlutusPrelude

import           Language.UntypedPlutusCore.Core
import           Language.UntypedPlutusCore.Evaluation.Machine.Cek.Internal
import           Language.UntypedPlutusCore.Subst

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Universe

import           Control.Lens                                               (AReview)
import           Control.Monad.Except
import           Control.Monad.Morph
import           Control.Monad.Reader
import           Control.Monad.ST
import           Control.Monad.State.Strict
import           Data.Array
import           Data.DList                                                 (DList)
import qualified Data.DList                                                 as DList
import           Data.HashMap.Monoidal
import           Data.STRef
import           Data.Semigroup.Generic
import           Data.Text.Prettyprint.Doc

-- TODO: don't forget StrictData!

type CekExTally fun = ExTally (ExBudgetCategory fun)

data ExBudgetMode st uni fun = ExBudgetMode
    { budgetModeSpender :: BudgetSpender st uni fun
    , budgetModeInitSt  :: st
    }

newtype CountingSt = CountingSt ExBudget
    deriving stock (Eq, Show)
    deriving newtype (Semigroup, Monoid, NFData)

data TallyingSt fun = TallyingSt (CekExTally fun) ExBudget
    deriving stock (Eq, Show, Generic)
    deriving (Semigroup, Monoid) via (GenericSemigroupMonoid (TallyingSt fun))
    deriving anyclass (NFData)

newtype RestrictingSt = RestrictingSt ExRestrictingBudget
    deriving stock (Eq, Show)
    deriving newtype (NFData)

monoidalBudgeting
    :: Monoid st => (ExBudgetCategory fun -> ExBudget -> st) -> ExBudgetMode st uni fun
monoidalBudgeting toSt = ExBudgetMode spender mempty where
    spender = BudgetSpender $ \key budgetToSpend -> modify' (<> toSt key budgetToSpend)

counting :: ExBudgetMode CountingSt uni fun
counting = monoidalBudgeting $ const CountingSt

tallying :: (Eq fun, Hashable fun) => ExBudgetMode (TallyingSt fun) uni fun
tallying =
    monoidalBudgeting $ \key budgetToSpend ->
        TallyingSt (ExTally $ singleton key budgetToSpend) budgetToSpend

restricting :: ExRestrictingBudget -> ExBudgetMode RestrictingSt uni fun
restricting = ExBudgetMode (BudgetSpender spend) . RestrictingSt where
    spend _ budgetToSpend = do
        RestrictingSt budgetLeft <- get
        let budgetLeft' = budgetLeft `minusExBudget` budgetToSpend
        -- Note that even if we throw an out-of-budget error, we still need to record
        -- what the final state was.
        put $! RestrictingSt budgetLeft'
        when (isNegativeBudget budgetLeft') $
            throwingWithCause _EvaluationError
                (UserEvaluationError $ CekOutOfExError budgetLeft')
                Nothing

-- | When we want to just evaluate the program we use the 'Restricting' mode with an enormous
-- budget, so that evaluation costs of on-chain budgeting are reflected accurately in benchmarks.
enormousBudget :: ExRestrictingBudget
enormousBudget = ExRestrictingBudget $ ExBudget (10^(10::Int)) (10^(10::Int))

restrictingEnormous :: ExBudgetMode RestrictingSt uni fun
restrictingEnormous = restricting enormousBudget

{- Note [CEK runners naming convention]
A function whose name ends in @NoEmit@ does not perform logging and so does not return any logs.
A function whose name starts with @unsafe@ throws exceptions instead of returning them purely.
A function from the @runCek@ family takes an 'ExExBudgetMode' parameter and returns the final
'CekExBudgetState' (and possibly logs).
A function from the @evaluateCek@ family does not return the final 'ExExBudgetMode', nor does it
allow one to specify an 'ExExBudgetMode'. I.e. such functions are only for fully evaluating programs
(and possibly returning logs). See also haddocks of 'enormousBudget'.
-}

-- | Evaluate a term using the CEK machine and keep track of costing, logging is optional.
runCek
    :: ( GShow uni, GEq uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , Hashable fun, Ix fun, ExMemoryUsage fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> ExBudgetMode st uni fun
    -> Bool
    -> Term Name uni fun ()
    -> (Either (CekEvaluationException uni fun) (Term Name uni fun ()), st, [String])
runCek runtime (ExBudgetMode spender st) emitting term =
    runCekM runtime spender st emitting $ do
        spendBudget BAST (ExBudget 0 (termAnn memTerm))
        computeCek [] mempty memTerm
  where
    memTerm = withMemory term

-- | Evaluate a term using the CEK machine with logging disabled and keep track of costing.
runCekNoEmit
    :: ( GShow uni, GEq uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , Hashable fun, Ix fun, ExMemoryUsage fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> ExBudgetMode st uni fun
    -> Term Name uni fun ()
    -> (Either (CekEvaluationException uni fun) (Term Name uni fun ()), st)
runCekNoEmit runtime mode term =
    case runCek runtime mode False term of
        (errOrRes, st', _) -> (errOrRes, st')

-- | Unsafely evaluate a term using the CEK machine with logging disabled and keep track of costing.
-- May throw a 'CekMachineException'.
unsafeRunCekNoEmit
    :: ( GShow uni, GEq uni, Typeable uni
       , Closed uni, uni `EverywhereAll` '[ExMemoryUsage, PrettyConst]
       , Hashable fun, Ix fun, Pretty fun, Typeable fun, ExMemoryUsage fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> ExBudgetMode st uni fun
    -> Term Name uni fun ()
    -> (EvaluationResult (Term Name uni fun ()), st)
unsafeRunCekNoEmit runtime mode =
    first unsafeExtractEvaluationResult . runCekNoEmit runtime mode

-- | Evaluate a term using the CEK machine with logging enabled.
evaluateCek
    :: ( GShow uni, GEq uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , Hashable fun, Ix fun, ExMemoryUsage fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> Term Name uni fun ()
    -> (Either (CekEvaluationException uni fun) (Term Name uni fun ()), [String])
evaluateCek runtime term =
    case runCek runtime restrictingEnormous True term of
        (errOrRes, _, logs) -> (errOrRes, logs)

-- | Evaluate a term using the CEK machine with logging disabled.
evaluateCekNoEmit
    :: ( GShow uni, GEq uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , Hashable fun, Ix fun, ExMemoryUsage fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> Term Name uni fun ()
    -> Either (CekEvaluationException uni fun) (Term Name uni fun ())
evaluateCekNoEmit runtime = fst . runCekNoEmit runtime restrictingEnormous

-- | Evaluate a term using the CEK machine with logging enabled. May throw a 'CekMachineException'.
unsafeEvaluateCek
    :: ( GShow uni, GEq uni, Typeable uni
       , Closed uni, uni `EverywhereAll` '[ExMemoryUsage, PrettyConst]
       , Hashable fun, Ix fun, Pretty fun, Typeable fun, ExMemoryUsage fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> Term Name uni fun ()
    -> (EvaluationResult (Term Name uni fun ()), [String])
unsafeEvaluateCek runtime = first unsafeExtractEvaluationResult . evaluateCek runtime

-- | Evaluate a term using the CEK machine with logging disabled. May throw a 'CekMachineException'.
unsafeEvaluateCekNoEmit
    :: ( GShow uni, GEq uni, Typeable uni
       , Closed uni, uni `EverywhereAll` '[ExMemoryUsage, PrettyConst]
       , Hashable fun, Ix fun, Pretty fun, Typeable fun, ExMemoryUsage fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> Term Name uni fun ()
    -> EvaluationResult (Term Name uni fun ())
unsafeEvaluateCekNoEmit runtime = unsafeExtractEvaluationResult . evaluateCekNoEmit runtime

-- | Unlift a value using the CEK machine.
readKnownCek
    :: ( GShow uni, GEq uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , KnownType (Term Name uni fun ()) a
       , Hashable fun, Ix fun, ExMemoryUsage fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> Term Name uni fun ()
    -> Either (CekEvaluationException uni fun) a
readKnownCek runtime = evaluateCekNoEmit runtime >=> readKnown
