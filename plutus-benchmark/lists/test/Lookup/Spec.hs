module Lookup.Spec (tests) where

import Test.Tasty
import Test.Tasty.Extras (TestNested, runTestGroupNestedGhc)

import PlutusBenchmark.Lists.Lookup.Compiled qualified as Compiled

import PlutusTx.Test qualified as Tx

-- Make a set of golden tests with results stored in a given subdirectory
-- inside a subdirectory determined by the GHC version.
testGroupGhcIn :: [FilePath] -> [TestNested] -> TestTree
testGroupGhcIn dir = runTestGroupNestedGhc (["lists", "test"] ++ dir)

tests :: TestTree
tests =
  testGroupGhcIn ["Lookup"] $
    flip concatMap sizes $ \sz ->
      [ Tx.goldenBudget ("match-scott-list-" ++ show sz) $
        Compiled.mkMatchWithListsCode (Compiled.workloadOfSize sz)
      , Tx.goldenBudget ("match-builtin-list-" ++ show sz) $
        Compiled.mkMatchWithBuiltinListsCode (Compiled.workloadOfSize sz)
      ]
  where
    sizes = [5, 10, 50, 100]
