{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

{- Note [Budgeting]

When running Plutus code on the chain, you're running code on other peoples machines, so you'll have to pay for it. And it has to be possible to determine how much money that should be before sending the transaction with the Plutus code to the chain. If you spend too little, your transaction will be rejected. If you spend too much, you're wasting money. So it must be possible to estimate how much a script will cost. The easiest way to do so is to run the script locally and determine the cost. The functional nature of Plutus allows for the assumption it will cost a similar amount locally as on the chain. See 'CekBudgetMode'.

Additionally, it's helpful to know which parts of the script cost how much. We assume it's useful to have a list of costs per term executed, so it's possible to estimate which parts of the script cost how much. The 'ExTally' has not been determined to be useful, but it was easy to implement.

We're tracking execution cost via both memory (via 'ExMemory') and CPU (via 'ExCPU'). Node operators are more interested in space limits than time limits - the memory upper limit will be reached faster than the time limit (which would be until next block). The two resources are then converted to the main currency of the chain based on protocol parameters - that way it's possible to adjust the actual fees without changing the code.

When tracking memory, we ignore garbage collection - only total memory allocation is counted. This decision decouples us from the implementation of the GC itself. Additioally, sharing of references is assumed. If a builtin generates a new value, every reference of that value (e.g. in different CEK environments) is assumed to point to the same value, without any copies. The CEK environment costs are included in the stack frame costs of the CEK machine, they're linear.

The tracking of the costs themselves does not cost anything. Currently that's an implementation detail. We may have to readjust this depending on real world experience. 

The CEK machine does budgeting in these steps:
- The memory cost of the initial AST is added to the budget. See Note [Memory Usage for Plutus]. This operation currently does not cost any CPU. It currently costs as much memory as the AST itself, before aborting. #1799
- Then each machine reduction step requires a certain amount of memory and CPU.
- The builtin operations may require different amounts of memory and CPU, depending on the input size.
- If a computation runs out of Memory or CPU, it is aborted.

Tracking CEK machine layers is rather straightfoward, albeit these numbers still have to be filled in. For builtins (e.g. +, etc.) the cost tracking can be a bit more complicated, as the required resources may depend on the size of the inputs. These cost estimations will also have factors attached which can be configured at runtime via protocol parameters - so it's possibel to easily adjust them at runtime.

-}

module Language.PlutusCore.Evaluation.Machine.ExBudgeting
    ( CekBudgetMode(..)
    , ExBudget(..)
    , ExBudgetState(..)
    , ExTally(..)
    , estimateStaticStagedCost
    , exBudgetCPU
    , exBudgetMemory
    , exTallyMemory
    , exTallyCPU
    , exBudgetStateBudget
    , exBudgetStateTally
    )
where


import           Language.PlutusCore
import           PlutusPrelude

import           Control.Lens.TH                                         (makeLenses)
import           Data.HashMap.Monoidal
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Evaluation.Machine.GenericSemigroup

data CekBudgetMode =
      Counting -- ^ For precalculation
    | Restricting -- ^ For execution, to avoid overruns

data ExBudget = ExBudget { _exBudgetCPU :: ExCPU, _exBudgetMemory :: ExMemory }
    deriving (Eq, Show, Generic)
    deriving (Semigroup, Monoid) via (GenericSemigroupMonoid ExBudget)

data ExBudgetState = ExBudgetState
    { _exBudgetStateTally  :: ExTally -- ^ for counting what cost how much
    , _exBudgetStateBudget :: ExBudget  -- ^ for making sure we don't spend too much
    }
    deriving stock (Eq, Generic, Show)

data ExTally = ExTally
    { _exTallyCPU    :: MonoidalHashMap (Plain Term) [ExCPU]
    , _exTallyMemory :: MonoidalHashMap (Plain Term) [ExMemory]
    }
    deriving stock (Eq, Generic, Show)
    deriving (Semigroup, Monoid) via (GenericSemigroupMonoid ExTally)

$(join <$> traverse makeLenses [''ExBudgetState, ''ExBudget, ''ExTally])

-- TODO See language-plutus-core/docs/Constant application.md for how to properly implement this
estimateStaticStagedCost
    :: BuiltinName -> [WithMemory Value] -> (ExCPU, ExMemory)
-- estimateStaticStagedCost AddInteger           [x, y] = (1, 1)
-- estimateStaticStagedCost SubtractInteger      [x, y] = (1, 1)
-- estimateStaticStagedCost MultiplyInteger      [x, y] = (1, 1)
-- estimateStaticStagedCost DivideInteger        [x, y] = (1, 1)
-- estimateStaticStagedCost QuotientInteger      [x, y] = (1, 1)
-- estimateStaticStagedCost RemainderInteger     [x, y] = (1, 1)
-- estimateStaticStagedCost ModInteger           [x, y] = (1, 1)
-- estimateStaticStagedCost LessThanInteger      [x, y] = (1, 1)
-- estimateStaticStagedCost LessThanEqInteger    [x, y] = (1, 1)
-- estimateStaticStagedCost GreaterThanInteger   [x, y] = (1, 1)
-- estimateStaticStagedCost GreaterThanEqInteger [x, y] = (1, 1)
-- estimateStaticStagedCost EqInteger            [x, y] = (1, 1)
-- estimateStaticStagedCost Concatenate          [x, y] = (1, 1)
-- estimateStaticStagedCost TakeByteString       [x, y] = (1, 1)
-- estimateStaticStagedCost DropByteString       [x, y] = (1, 1)
-- estimateStaticStagedCost SHA2                 x      = (1, 1)
-- estimateStaticStagedCost SHA3                 x      = (1, 1)
-- estimateStaticStagedCost VerifySignature      [x, y] = (1, 1)
-- estimateStaticStagedCost EqByteString         [x, y] = (1, 1)
-- estimateStaticStagedCost LtByteString         [x, y] = (1, 1)
-- estimateStaticStagedCost GtByteString         [x, y] = (1, 1)
estimateStaticStagedCost _ _ = (1, 1)
