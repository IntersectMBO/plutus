{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TypeApplications #-}
module Spec.Marlowe.ACTUS
    (
      tests, TestCase(..)
    )
where

import qualified Data.List                                         as L (find)
import qualified Data.Map                                          as M (lookup)
import           Data.Maybe                                        (fromMaybe)
import           GHC.Records                                       (getField)
import           Language.Marlowe.ACTUS.Analysis                   (genProjectedCashflows)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents (EventType (..), RiskFactorsPoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms  hiding (Assertion)
import           Language.Marlowe.ACTUS.Definitions.Schedule
import           Spec.Marlowe.Util
import           Test.Tasty
import           Test.Tasty.HUnit

tests :: String -> [TestCase] -> TestTree
tests n t = testGroup n $ [ testCase (getField @"identifier" tc) (runTest tc) | tc <- t]

runTest :: TestCase -> Assertion
runTest tc@TestCase {..} =
  let testcase = testToContractTerms tc
      contract = setDefaultContractTermValues testcase
      observed = parseObservedValues dataObserved

      getRiskFactors ev date =
        let riskFactors =
              RiskFactorsPoly
                { o_rf_CURS = 1.0,
                  o_rf_RRMO = 1.0,
                  o_rf_SCMO = 1.0,
                  pp_payoff = 0.0
                }

            observedKey RR = ct_RRMO contract
            observedKey SC = ct_SCMO contract
            observedKey _  = ct_CURS contract

            value = fromMaybe 1.0 $ do
              k <- observedKey ev
              ValuesObserved {values = values} <- M.lookup k observed
              ValueObserved {value = valueObserved} <- L.find (\ValueObserved {timestamp = timestamp} -> timestamp == date) values
              return valueObserved
         in case ev of
              RR -> riskFactors {o_rf_RRMO = value}
              SC -> riskFactors {o_rf_SCMO = value}
              _  -> riskFactors {o_rf_CURS = value}

      cashFlows = genProjectedCashflows getRiskFactors contract
      cashFlowsTo = maybe cashFlows (\d -> filter (\cf -> cashCalculationDay cf <= d) cashFlows) (parseDate to)
   in assertTestResults cashFlowsTo results identifier
