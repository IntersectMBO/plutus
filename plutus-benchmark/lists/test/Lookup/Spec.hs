module Lookup.Spec (tests) where

import Test.Tasty
import Test.Tasty.Extras (TestNested, runTestNested, testNestedGhc)

import PlutusBenchmark.Lists.Lookup.Compiled qualified as Compiled

import PlutusTx.Test qualified as Tx

-- Make a set of golden tests with results stored in a given subdirectory
-- inside a subdirectory determined by the GHC version.
runTestGhc :: [FilePath] -> [TestNested] -> TestTree
runTestGhc path = runTestNested (["lists", "test"] ++ path) . pure . testNestedGhc

tests :: TestTree
tests =
  runTestGhc ["Lookup"] $
    flip concatMap sizes $ \sz ->
      [ Tx.goldenEvalCekCatchBudget ("match-scott-list-" ++ show sz) $
          Compiled.mkMatchWithListsCode (Compiled.workloadOfSize sz)
      , Tx.goldenEvalCekCatchBudget ("match-builtin-list-" ++ show sz) $
          Compiled.mkMatchWithBuiltinListsCode (Compiled.workloadOfSize sz)
      ]
  where
    sizes = [5, 10, 50, 100]
