{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}

module Spec.Marlowe.ACTUS.QCTests
  ( tests )
where

import           Data.Time                                                (LocalTime)
import           Data.Validation                                          as V
import           Language.Marlowe.ACTUS.Analysis
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents
import           Language.Marlowe.ACTUS.Definitions.ContractTerms
import           Language.Marlowe.ACTUS.Definitions.Schedule
import           Language.Marlowe.ACTUS.Model.APPLICABILITY.Applicability
import           Spec.Marlowe.ACTUS.QCGenerator
import           Test.QuickCheck
import           Test.Tasty
import           Test.Tasty.QuickCheck

import           Debug.Pretty.Simple

tests :: TestTree
tests = testGroup "QuickCheck"
  [ testProperty "Non empty cashflows" prop_non_empty
  -- , testProperty "Last event" prop_terminal_event
  ]

newtype ContractTermsQC = ContractTermsQC ContractTerms deriving (Show)

instance Arbitrary ContractTermsQC where
  arbitrary = ContractTermsQC . setDefaultContractTermValues <$> contractTermsGen

validContract :: ContractTerms -> Bool
validContract ct = case validateTerms ct of
  V.Success _ -> True
  V.Failure _ -> False

defaultRiskFactors :: EventType -> LocalTime -> RiskFactors
defaultRiskFactors _ _ =
  RiskFactorsPoly
    { o_rf_CURS = 1.0,
      o_rf_RRMO = 1.0,
      o_rf_SCMO = 1.0,
      pp_payoff = 0.0
    }

prop_non_empty :: ContractTermsQC -> Property
prop_non_empty (ContractTermsQC ct) = validContract ct ==>
  let cf = genProjectedCashflows defaultRiskFactors ct
   in not (null cf)

prop_terminal_event :: ContractTermsQC -> Property
prop_terminal_event (ContractTermsQC ct) = validContract ct ==>
  let cf = genProjectedCashflows defaultRiskFactors ct
   in pTraceShow (last cf) $ cashEvent (last cf) `elem` [MD, TD]
