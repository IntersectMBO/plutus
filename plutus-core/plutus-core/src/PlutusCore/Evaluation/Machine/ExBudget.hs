{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE UndecidableInstances   #-}

{-# LANGUAGE StrictData             #-}

{- Note [Strict Data for budgeting]

Without the StrictData pragma here, we get a memory leak during evaluation
because large unevaluated arthimetic expressions build up.  Strictness is only
really required for ExBudget, but it's simpler if we jut make
everything strict, and it doesn't seem to do any harm.
-}

{- Note [Budgeting]

When running Plutus code on the chain, you're running code on other peoples
machines, so you'll have to pay for it. And it has to be possible to determine
how much money that should be before sending the transaction with the Plutus
code to the chain. If you spend too little, your transaction will be rejected.
If you spend too much, you're wasting money. So it must be possible to estimate
how much a script will cost. The easiest way to do so is to run the script
locally and determine the cost. The functional nature of Plutus allows for the
assumption it will cost a similar amount locally as on the chain. See
'CekBudgetMode'.

Additionally, it's helpful to know which parts of the script cost how much. We
assume it's useful to have a list of costs per term executed, so it's possible
to estimate which parts of the script cost how much. The 'ExTally' has not been
determined to be useful, but it was easy to implement.

We're tracking execution cost via both memory (via 'ExMemory') and CPU (via
'ExCPU'). Node operators are more interested in space limits than time limits -
the memory upper limit will be reached faster than the time limit (which would
be until next block). The two resources are then converted to the main currency
of the chain based on protocol parameters - that way it's possible to adjust the
actual fees without changing the code.

When tracking memory, we ignore garbage collection - only total memory
allocation is counted. This decision decouples us from the implementation of the
GC itself. Additionally, sharing of references is assumed. If a builtin
generates a new value, every reference of that value (e.g. in different CEK
environments) is assumed to point to the same value, without any copies. So the
total memory of the program is bounded to the original program + anything the
builtins produce + the machine space used by the CEK machine itself. The CEK
environment costs are included in the stack frame costs of the CEK machine,
they're linear.

The tracking of the costs themselves does not cost any CPU or memory. Currently
that's an implementation detail. We may have to readjust this depending on real
world experience.

The CEK machine does budgeting in these steps:
- The memory cost of the initial AST is added to the budget. See Note [Memory
  Usage for Plutus]. This operation currently does not cost any CPU. It
  currently costs as much memory as the AST itself, before aborting. See
  https://github.com/input-output-hk/plutus/issues/1799 for more discussion.
- Then each machine reduction step requires a certain amount of memory and CPU.
- The builtin operations may require different amounts of memory and CPU,
  depending on the input size.
- If a computation runs out of Memory or CPU, it is aborted, via the same
  mechanism when 'error' is called.

Tracking CEK machine layers is rather straightforward, albeit these numbers
still have to be filled in. For builtins (e.g. +, etc.) the cost tracking can be
a bit more complicated, as the required resources may depend on the size of the
inputs (E.g. multiplying numbers, where the output will be around 6 words if
both inputs are at 3 words each). These cost estimations will also have factors
attached which can be configured at runtime via protocol parameters - so it's
possible to adjust them at runtime.

-}

module PlutusCore.Evaluation.Machine.ExBudget
    ( ExBudget(..)
    , ToExMemory(..)
    , ExBudgetBuiltin(..)
    , SpendBudget(..)
    , ExRestrictingBudget(..)
    , isNegativeBudget
    , minusExCPU
    , minusExMemory
    , minusExBudget
    )
where

import           PlutusPrelude                          hiding (toList)

import           PlutusCore.Core
import           PlutusCore.Name

import           Control.Monad.Except
import           Data.Semigroup.Generic
import           Data.Text.Prettyprint.Doc
import           PlutusCore.Evaluation.Machine.ExMemory

class ToExMemory term where
    -- | Get the 'ExMemory' of a @term@. If the @term@ is not annotated with 'ExMemory', then
    -- return something arbitrary just to fit such a term into the builtin application machinery.
    toExMemory :: term -> ExMemory

instance ToExMemory (Term TyName Name uni fun ()) where
    toExMemory _ = 0

instance ToExMemory (Term TyName Name uni fun ExMemory) where
    toExMemory = termAnn

-- | A class for injecting a 'Builtin' into an @exBudgetCat@.
-- We need it, because the constant application machinery calls 'spendBudget' before reducing a
-- constant application and we want to be general over @exBudgetCat@ there, but still track the
-- built-in functions category, hence the ad hoc polymorphism.
class ExBudgetBuiltin fun exBudgetCat where
    exBudgetBuiltin :: fun -> exBudgetCat

-- | A dummy 'ExBudgetBuiltin' instance to be used in monads where we don't care about costing.
instance ExBudgetBuiltin fun () where
    exBudgetBuiltin _ = ()

-- This works nicely because @m@ contains @term@.
class (ExBudgetBuiltin fun exBudgetCat) =>
            SpendBudget m fun exBudgetCat | m -> fun exBudgetCat where
    -- | Spend the budget, which may mean different things depending on the monad:
    --
    -- 1. do nothing for an evaluator that does not care about costing
    -- 2. count upwards to get the cost of a computation
    -- 3. subtract from the current budget and fail if the budget goes below zero
    spendBudget :: exBudgetCat -> ExBudget -> m ()

instance (Monad m, SpendBudget m fun exBudgetCat) => SpendBudget (ExceptT e m) fun exBudgetCat where
    spendBudget c b  = lift $ spendBudget c b

data ExBudget = ExBudget { _exBudgetCPU :: ExCPU, _exBudgetMemory :: ExMemory }
    deriving stock (Eq, Show, Generic)
    deriving (Semigroup, Monoid) via (GenericSemigroupMonoid ExBudget)
    deriving anyclass (PrettyBy config, NFData)

instance Pretty ExBudget where
    pretty (ExBudget cpu memory) = parens $ fold
        [ "{ cpu: ", pretty cpu, line
        , "| mem: ", pretty memory, line
        , "}"
        ]

newtype ExRestrictingBudget = ExRestrictingBudget ExBudget deriving (Show, Eq)
    deriving (Semigroup, Monoid) via (GenericSemigroupMonoid ExBudget)
    deriving newtype (Pretty, PrettyBy config, NFData)

isNegativeBudget :: ExRestrictingBudget -> Bool
isNegativeBudget (ExRestrictingBudget (ExBudget cpu mem)) = cpu < 0 || mem < 0

-- | @(-)@ on 'ExCPU'.
minusExCPU :: ExCPU -> ExCPU -> ExCPU
minusExCPU = coerce $ (-) @Integer

-- | @(-)@ on 'ExMemory'.
minusExMemory :: ExMemory -> ExMemory -> ExMemory
minusExMemory = coerce $ (-) @Integer

-- | Subtract an 'ExBudget' from an 'ExRestrictingBudget'.
minusExBudget :: ExRestrictingBudget -> ExBudget -> ExRestrictingBudget
ExRestrictingBudget (ExBudget cpuL memL) `minusExBudget` ExBudget cpuR memR =
    ExRestrictingBudget $ ExBudget (cpuL `minusExCPU` cpuR) (memL `minusExMemory` memR)
