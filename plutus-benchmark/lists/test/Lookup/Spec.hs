module Lookup.Spec (tests) where

import Data.Foldable (for_)
import Test.Tasty
import Test.Tasty.Extras (TestNested, runTestNestedM, testNestedGhcM)

import PlutusBenchmark.Lists.Lookup.Compiled qualified as Compiled

import PlutusTx.Test qualified as Tx

-- Make a set of golden tests with results stored in a given subdirectory
-- inside a subdirectory determined by the GHC version.
runTestGhcInM :: [FilePath] -> TestNested -> TestTree
runTestGhcInM path = runTestNestedM (["lists", "test"] ++ path) . testNestedGhcM

tests :: TestTree
tests =
  runTestGhcInM ["Lookup"] $
    for_ sizes $ \sz -> do
      Tx.goldenBudget ("match-scott-list-" ++ show sz) $
        Compiled.mkMatchWithListsCode (Compiled.workloadOfSize sz)
      Tx.goldenBudget ("match-builtin-list-" ++ show sz) $
        Compiled.mkMatchWithBuiltinListsCode (Compiled.workloadOfSize sz)
  where
    sizes = [5, 10, 50, 100]
