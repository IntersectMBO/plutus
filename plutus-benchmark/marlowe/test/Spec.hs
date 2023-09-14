-- Budget tests for Marlowe scripts
{-# LANGUAGE RecordWildCards #-}

module Main (main) where

import Test.Tasty
import Test.Tasty.Extras

import PlutusBenchmark.Marlowe.BenchUtil (benchmarkToUPLC, rolePayoutBenchmarks,
                                          semanticsBenchmarks)
import PlutusBenchmark.Marlowe.Scripts.RolePayout (rolePayoutValidator)
import PlutusBenchmark.Marlowe.Scripts.Semantics (marloweValidator)
import PlutusBenchmark.Marlowe.Types qualified as M
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Test (goldenUPlcBudget)
import PlutusLedgerApi.V2 (scriptContextTxInfo, txInfoId)
import PlutusTx.Code (CompiledCode)
import UntypedPlutusCore (NamedDeBruijn)
import UntypedPlutusCore.Core.Type qualified as UPLC

mkBudgetTest ::
    CompiledCode a
    -> M.Benchmark
    -> (String, [UPLC.Program NamedDeBruijn DefaultUni DefaultFun ()])
mkBudgetTest validator bm@M.Benchmark{..} =
  let benchName = show $ txInfoId $ scriptContextTxInfo bScriptContext
  in
    (benchName, [benchmarkToUPLC validator bm])

main :: IO ()
main = do

  -- Read the semantics benchmark files.
  semanticsMBench <- either error id <$> semanticsBenchmarks

  -- Read the role payout benchmark files.
  rolePayoutMBench <- either error id <$> rolePayoutBenchmarks

  let allTests :: TestTree
      allTests =
        testGroup "plutus-benchmark Marlowe tests"
            [ runTestNestedIn ["marlowe", "test"] $ testNested "semantics" $
                map (uncurry goldenUPlcBudget . mkBudgetTest marloweValidator) semanticsMBench
            , runTestNestedIn ["marlowe", "test"] $ testNested "role-payout" $
                map (uncurry goldenUPlcBudget . mkBudgetTest rolePayoutValidator) rolePayoutMBench
            ]
  defaultMain allTests
