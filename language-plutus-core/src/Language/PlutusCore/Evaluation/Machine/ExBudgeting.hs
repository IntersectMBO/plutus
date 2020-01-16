{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

{- Note [Budgeting]

Each operation costs a certain amount of memory and CPU.
For memory Plutus counts this usage via ExMemory units, which correspond to machine words (64bit).
For CPU, it's ExCPU, which does not have a base as just yet.

First, the memory cost of the initial AST is added to the budget. See 'ExMemoryUsage'.
Then each machine requires a certain amount of memory and CPU.
The builtin operations may require different amounts of budget, depending on the input size.

If a computation runs out of Memory or CPU, it is aborted.

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
      Counting -- ^ Counts up
    | Restricting -- ^ Counts down and stops execution


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

-- TODO invalid number of args
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
estimateStaticStagedCost _ _ = (1, 1) -- TODO
