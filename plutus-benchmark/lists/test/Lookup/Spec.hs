module Lookup.Spec (tests) where

import Data.Traversable (for)
import Test.Tasty
import Test.Tasty.Extras (runTestNestedIn, testNestedGhcM)

import PlutusBenchmark.Lists.Lookup.Compiled qualified as Compiled

import PlutusTx.Test qualified as Tx

tests :: TestTree
tests =
  -- Make a set of golden tests with results stored in a given subdirectory
  -- inside a subdirectory determined by the GHC version.
  runTestNestedIn ["lists", "test", "Lookup"] . testNestedGhcM $
    for sizes $ \sz -> do
      Tx.goldenBudget ("match-scott-list-" ++ show sz) $
        Compiled.mkMatchWithListsCode (Compiled.workloadOfSize sz)
      Tx.goldenBudget ("match-builtin-list-" ++ show sz) $
        Compiled.mkMatchWithBuiltinListsCode (Compiled.workloadOfSize sz)
  where
    sizes = [5, 10, 50, 100]
