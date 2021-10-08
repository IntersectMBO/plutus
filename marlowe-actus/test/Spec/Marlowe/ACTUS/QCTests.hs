{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}

module Spec.Marlowe.ACTUS.QCTests
  ( tests )
where

import           Data.Maybe                                               (isJust)
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

tests :: TestTree
tests = testGroup "QuickCheck"
  [ testProperty "Non empty cashflows" prop_non_empty
  , testProperty "Purchase event" prop_purchase
  , testProperty "Principal repayment (PAM)" prop_principal_payment
  ]

newtype ContractTermsQC = ContractTermsQC ContractTerms deriving (Show)
newtype ContractTermsPAM = ContractTermsPAM ContractTerms deriving (Show)
newtype ContractTermsLAM = ContractTermsLAM ContractTerms deriving (Show)
newtype ContractTermsNAM = ContractTermsNAM ContractTerms deriving (Show)
newtype ContractTermsANN = ContractTermsANN ContractTerms deriving (Show)

instance Arbitrary ContractTermsQC where
  arbitrary = ContractTermsQC . setDefaultContractTermValues <$> contractTermsGen

instance Arbitrary ContractTermsPAM where
  arbitrary = ContractTermsPAM . setDefaultContractTermValues <$> contractTermsGen' PAM

instance Arbitrary ContractTermsLAM where
  arbitrary = ContractTermsLAM . setDefaultContractTermValues <$> contractTermsGen' LAM

instance Arbitrary ContractTermsNAM where
  arbitrary = ContractTermsNAM . setDefaultContractTermValues <$> contractTermsGen' NAM

instance Arbitrary ContractTermsANN where
  arbitrary = ContractTermsANN . setDefaultContractTermValues <$> contractTermsGen' ANN

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
prop_non_empty (ContractTermsQC ct) =
  validContract ct
    ==> let cf = genProjectedCashflows defaultRiskFactors ct
         in not (null cf)

prop_purchase :: ContractTermsQC -> Property
prop_purchase (ContractTermsQC ct) =
  validContract ct && isJust (ct_PRD ct)
    ==> let cf = genProjectedCashflows defaultRiskFactors ct
         in PRD `elem` map cashEvent cf

prop_principal_payment :: ContractTermsPAM -> Property
prop_principal_payment (ContractTermsPAM ct) =
  validContract ct && isJust (ct_IPANX ct)
    ==> let cf =
              genProjectedCashflows
                defaultRiskFactors
                ct
                  { ct_PRD = Nothing,
                    ct_TD = Nothing,
                    ct_SCNT = Just 1.0,
                    ct_SCIP = Just 1.0,
                    ct_FER = Just 0.0,
                    ct_PDIED = Just 0.0,
                    ct_IPAC = Just 0.0,
                    ct_IPCBA = Just 0.0,
                    ct_IPCB = Nothing,
                    ct_SCANX = Nothing,
                    ct_IPCED = Nothing,
                    ct_SCEF = Nothing,
                    ct_FEAC = Nothing,
                    ct_SCCL = Nothing,
                    ct_RRCL = Nothing
                  }
            ied = sum $ map amount $ filter (\c -> cashEvent c == IED) cf
            md = sum $ map amount $ filter (\c -> cashEvent c == MD) cf
         in ied + md == 0.0
