-- Budget tests for Marlowe scripts
{-# LANGUAGE RecordWildCards #-}

module Main (main) where

import Test.Tasty
import Test.Tasty.Extras (TestNested, runTestGroupNestedGhc)

import PlutusBenchmark.Marlowe.BenchUtil (benchmarkToUPLC, rolePayoutBenchmarks,
                                          semanticsBenchmarks)
import PlutusBenchmark.Marlowe.Scripts.RolePayout (rolePayoutValidator)
import PlutusBenchmark.Marlowe.Scripts.Semantics (marloweValidator)
import PlutusBenchmark.Marlowe.Types qualified as M
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Test (goldenUEvalBudget)
import PlutusLedgerApi.V2 (scriptContextTxInfo, txInfoId)
import PlutusTx.Code (CompiledCode)
import PlutusTx.Test
import UntypedPlutusCore (NamedDeBruijn)
import UntypedPlutusCore.Core.Type qualified as UPLC

mkBudgetTest ::
    CompiledCode a
    -> M.Benchmark
    -> (String, UPLC.Program NamedDeBruijn DefaultUni DefaultFun ())
mkBudgetTest validator bm@M.Benchmark{..} =
  let benchName = show $ txInfoId $ scriptContextTxInfo bScriptContext
  in
    (benchName, benchmarkToUPLC validator bm)

-- Make a set of golden tests with results stored in a given subdirectory
-- inside a subdirectory determined by the GHC version.
testGroupGhcIn :: [FilePath] -> [TestNested] -> TestTree
testGroupGhcIn path = runTestGroupNestedGhc (["marlowe", "test"] ++ path)

main :: IO ()
main = do

  -- Read the semantics benchmark files.
  semanticsMBench <- either error id <$> semanticsBenchmarks

  -- Read the role payout benchmark files.
  rolePayoutMBench <- either error id <$> rolePayoutBenchmarks

  let allTests :: TestTree
      allTests =
        testGroup "plutus-benchmark Marlowe tests"
            [ testGroupGhcIn ["semantics"] $
                goldenSize "semantics" marloweValidator
                  : [ goldenUEvalBudget name [value]
                    | bench <- semanticsMBench
                    , let (name, value) = mkBudgetTest marloweValidator bench
                    ]
            , testGroupGhcIn ["role-payout"] $
                goldenSize "role-payout" rolePayoutValidator
                  : [ goldenUEvalBudget name [value]
                    | bench <- rolePayoutMBench
                    , let (name, value) = mkBudgetTest rolePayoutValidator bench
                    ]
            ]
  defaultMain allTests
