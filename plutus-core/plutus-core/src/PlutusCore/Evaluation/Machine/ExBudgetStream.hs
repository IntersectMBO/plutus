{-# LANGUAGE BangPatterns #-}

module PlutusCore.Evaluation.Machine.ExBudgetStream
  ( ExBudgetStream (..)
  , sumExBudgetStream
  , zipCostStream
  ) where

import PlutusCore.Evaluation.Machine.CostStream
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExMemory

import Data.Coerce

{-| A lazy stream of 'ExBudget's. Basically @NonEmpty ExBudget@, except the elements are
stored strictly.

The semantics of a stream are those of the 'fold' of its elements. I.e. a stream that is a
reordered version of another stream is considered equal to that stream.

An 'ExBudgetStream' is what one gets by zipping two 'CostStream's (one for CPU, one for memory),
which is why the two data types are so similar. The only reason why we don't express both the
concepts in terms of a single data type is efficiency, in particular unboxing is crucial for
'CostStream' and we don't care about it in 'ExBudgetStream', because we can't get the spender
in the CEK machine to get inlined and so unboxing 'ExBudget' here would only result in boxing it
back once it's about to be spent. -}
data ExBudgetStream
  = ExBudgetLast !ExBudget
  | ExBudgetCons !ExBudget ExBudgetStream
  deriving stock (Show)

-- See Note [Global local functions].
sumExBudgetStreamGo :: ExBudget -> ExBudgetStream -> ExBudget
sumExBudgetStreamGo !acc (ExBudgetLast budget) = acc <> budget
sumExBudgetStreamGo !acc (ExBudgetCons budget budgets) = sumExBudgetStreamGo (acc <> budget) budgets

-- | Add up all the budgets in a 'ExBudgetStream'.
sumExBudgetStream :: ExBudgetStream -> ExBudget
sumExBudgetStream (ExBudgetLast budget0) = budget0
sumExBudgetStream (ExBudgetCons budget0 budgets0) = sumExBudgetStreamGo budget0 budgets0
{-# INLINE sumExBudgetStream #-}

-- | Convert a 'CostStream' to an 'ExBudgetStream' by applying a function to each element.
costToExBudgetStream :: (CostingInteger -> ExBudget) -> CostStream -> ExBudgetStream
costToExBudgetStream f = go
  where
    go (CostLast cost) = ExBudgetLast (f cost)
    go (CostCons cost costs) = ExBudgetCons (f cost) $ go costs
{-# INLINE costToExBudgetStream #-}

{-| Convert a 'CostingInteger' representing a CPU cost and a 'CostingInteger' representing a memory
cost to an 'ExBudget'. -}
toExBudget :: CostingInteger -> CostingInteger -> ExBudget
toExBudget = coerce ExBudget
{-# INLINE toExBudget #-}

-- See Note [Global local functions].
zipCostStreamGo :: CostStream -> CostStream -> ExBudgetStream
zipCostStreamGo (CostLast cpu) (CostLast mem) =
  ExBudgetLast $ toExBudget cpu mem
zipCostStreamGo (CostLast cpu) (CostCons mem mems) =
  ExBudgetCons (toExBudget cpu mem) $ costToExBudgetStream (\mem' -> toExBudget 0 mem') mems
zipCostStreamGo (CostCons cpu cpus) (CostLast mem) =
  ExBudgetCons (toExBudget cpu mem) $ costToExBudgetStream (\cpu' -> toExBudget cpu' 0) cpus
zipCostStreamGo (CostCons cpu cpus) (CostCons mem mems) =
  ExBudgetCons (toExBudget cpu mem) $ zipCostStreamGo cpus mems

{-| Zip two 'CostStream' together (one with CPU costs and the other one with memory costs,
respectively) to get an 'ExBudgetStream'. If one is longer than the other, then it's assumed to
contain the required amount of zeros for two streams to have the same length (all those zeros
\"appear\" in the tail of the stream). -}
zipCostStream :: CostStream -> CostStream -> ExBudgetStream
zipCostStream cpus0 mems0 = case (cpus0, mems0) of
  -- See Note [Single-element streams].
  (CostLast cpu, CostLast mem) -> ExBudgetLast $ toExBudget cpu mem
  _ -> zipCostStreamGo cpus0 mems0
{-# INLINE zipCostStream #-}
