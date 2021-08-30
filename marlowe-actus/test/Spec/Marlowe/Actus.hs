{-# LANGUAGE RecordWildCards #-}
module Spec.Marlowe.Actus
    (
      tests, TestCase(..)
    )
where

import           Language.Marlowe.ACTUS.Analysis                  (genProjectedCashflows)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms hiding (Assertion)
import           Language.Marlowe.ACTUS.Definitions.Schedule
import           Spec.Marlowe.Util
import           Test.Tasty
import           Test.Tasty.HUnit

tests :: String -> [TestCase] -> TestTree
tests n t = testGroup n $ [ testCase (identifier tc) (runTest tc) | tc <- t]

runTest :: TestCase -> Assertion
runTest tc@TestCase{..} =
  let testcase = testToContractTerms tc
      contract = setDefaultContractTermValues testcase
      observed = parseObservedValues dataObserved
      cashFlows = genProjectedCashflows observed contract
      cashFlowsTo = maybe cashFlows (\d -> filter (\cf -> cashCalculationDay cf <= d) cashFlows) (parseDate to)
  in assertTestResults cashFlowsTo results identifier
