{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}

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

module Language.PlutusCore.Evaluation.Machine.ExBudgeting
    ( ExBudgetMode(..)
    , ExBudget(..)
    , ExBudgetState(..)
    , ExTally(..)
    , ExBudgetCategory(..)
    , ExRestrictingBudget(..)
    , SpendBudget(..)
    , estimateStaticStagedCost
    , exBudgetCPU
    , exBudgetMemory
    , exBudgetStateBudget
    , exBudgetStateTally
    , exceedsBudget
    )
where


import           Language.PlutusCore.Core.Type
import           PlutusPrelude

import           Control.Lens.Indexed
import           Control.Lens.TH                                         (makeLenses)
import           Data.Hashable
import           Data.HashMap.Monoidal
import           Data.List                                               (intersperse)
import           Data.Text.Prettyprint.Doc
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Evaluation.Machine.GenericSemigroup

newtype ExRestrictingBudget = ExRestrictingBudget ExBudget deriving (Show, Eq)
    deriving (Semigroup, Monoid) via (GenericSemigroupMonoid ExBudget)

data ExBudgetMode =
      Counting -- ^ For precalculation
    | Restricting ExRestrictingBudget -- ^ For execution, to avoid overruns

class SpendBudget m where
    spendBudget :: ExBudgetCategory -> WithMemory Term -> ExBudget -> m ()

data ExBudgetCategory
    = BTyInst
    | BApply
    | BIWrap
    | BUnwrap
    | BVar
    | BBuiltin StagedBuiltinName
    | BAST
    deriving stock (Show, Eq, Generic)
instance Hashable ExBudgetCategory
instance (PrettyBy config) ExBudgetCategory where
    prettyBy _ = viaShow

data ExBudget = ExBudget { _exBudgetCPU :: ExCPU, _exBudgetMemory :: ExMemory }
    deriving (Eq, Show, Generic)
    deriving (Semigroup, Monoid) via (GenericSemigroupMonoid ExBudget)
instance PrettyBy config ExBudget where
    prettyBy config (ExBudget cpu memory) = parens $ fold
        [ "{ cpu: ", prettyBy config cpu, line
        , "| mem: ", prettyBy config memory, line
        , "}"
        ]

data ExBudgetState = ExBudgetState
    { _exBudgetStateTally  :: ExTally -- ^ for counting what cost how much
    , _exBudgetStateBudget :: ExBudget  -- ^ for making sure we don't spend too much
    }
    deriving stock (Eq, Generic, Show)
instance PrettyBy config ExBudgetState where
    prettyBy config (ExBudgetState tally budget) = parens $ fold
        [ "{ tally: ", prettyBy config tally, line
        , "| budget: ", prettyBy config budget, line
        , "}"
        ]

newtype ExTally = ExTally (MonoidalHashMap ExBudgetCategory ExBudget)
    deriving stock (Eq, Generic, Show)
    deriving (Semigroup, Monoid) via (GenericSemigroupMonoid ExTally)
instance PrettyBy config ExTally where
    prettyBy config (ExTally m) =
        parens $ fold (["{ "] <> (intersperse (line <> "| ") $ fmap group $
          ifoldMap (\k v -> [(prettyBy config k <+> "causes" <+> prettyBy config v)]) m) <> ["}"])

$(mtraverse makeLenses [''ExBudgetState, ''ExBudget])

-- TODO See language-plutus-core/docs/Constant application.md for how to properly implement this
estimateStaticStagedCost
    :: BuiltinName -> [WithMemory Value] -> (ExCPU, ExMemory)
estimateStaticStagedCost _ _ = (1, 1)

exceedsBudget :: ExRestrictingBudget -> ExBudget -> Bool
exceedsBudget (ExRestrictingBudget ex) budget = (view exBudgetCPU budget) > (view exBudgetCPU ex) || (view exBudgetMemory budget) > (view exBudgetMemory ex)
