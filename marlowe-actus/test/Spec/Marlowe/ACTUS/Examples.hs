{-# LANGUAGE OverloadedStrings #-}
module Spec.Marlowe.ACTUS.Examples
    (tests)
where

import           Data.Maybe                                       (fromJust)
import           Data.Time.Format.ISO8601
import           Data.Validation                                  (Validation (..))
import           Language.Marlowe
import           Language.Marlowe.ACTUS.Definitions.ContractTerms
import           Language.Marlowe.ACTUS.Generator
import qualified Ledger.Value                                     as Val
import           Test.Tasty
import           Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "Marlowe represenation of sample ACTUS contracts"
  [
    testCase "PAM example01" example01
  , testCase "LAM example02" example02
  , testCase "NAM example03" example03
  , testCase "ANN example04" example04
  ]

-- |example01 defines a contract of type PAM
--
-- principal: 10000
-- interest rate: 2% p.a.
-- annual interest payments
-- term: 10 years
--
-- cashflows:
-- 0 : -10000
-- 1 :    200
-- 2 :    200
-- 3 :    200
-- 4 :    200
-- 5 :    200
-- 6 :    200
-- 7 :    200
-- 8 :    200
-- 9 :    200
-- 10:  10200
example01 :: IO ()
example01 =
  let ct =
        ContractTermsPoly
          { contractId = "0",
            contractType = PAM,
            ct_IED = iso8601ParseM "2020-01-01T00:00:00",
            ct_SD = fromJust $ iso8601ParseM "2019-12-31T00:00:00",
            ct_MD = iso8601ParseM "2030-01-01T00:00:00",
            ct_AD = Nothing,
            ct_TD = Nothing,
            ct_PRNXT = Nothing,
            ct_PRD = Nothing,
            ct_CNTRL = CR_RPA,
            ct_PDIED = Nothing,
            ct_NT = Just 10000.0,
            ct_PPRD = Nothing,
            ct_PTD = Nothing,
            ct_DCC = Just DCC_E30_360,
            ct_PPEF = Just PPEF_N,
            ct_PRF = Just PRF_PF,
            scfg =
              ScheduleConfig
                { calendar = Just CLDR_NC,
                  eomc = Just EOMC_EOM,
                  bdc = Just BDC_NULL
                },
            -- Penalties
            ct_PYRT = Nothing,
            ct_PYTP = Just PYTP_O, -- no penalty
            -- Optionality
            ct_OPCL = Nothing,
            ct_OPANX = Nothing,
            -- Scaling
            ct_SCIP = Nothing,
            ct_SCIED = Nothing,
            ct_SCEF = Nothing,
            ct_SCCDD = Nothing,
            ct_SCMO = Nothing,
            ct_SCNT = Nothing,
            ct_SCCL = Nothing,
            ct_SCANX = Nothing,
            -- Rate Reset
            ct_RRCL = Nothing,
            ct_RRANX = Nothing,
            ct_RRNXT = Nothing,
            ct_RRSP = Nothing,
            ct_RRMLT = Nothing,
            ct_RRMO = Nothing,
            ct_RRPF  = Nothing,
            ct_RRPC  = Nothing,
            ct_RRLC  = Nothing,
            ct_RRLF  = Nothing,
            -- Interest
            ct_IPCED = Nothing,
            ct_IPCL = Just $ Cycle 1 P_Y ShortStub False,
            ct_IPANX = iso8601ParseM "2020-01-01T00:00:00",
            ct_IPNR = Just 0.02,
            ct_IPAC = Just 0.0,
            ct_PRCL = Nothing,
            ct_PRANX = Nothing,
            ct_IPCB = Just IPCB_NT,
            ct_IPCBA = Nothing,
            ct_IPCBCL = Nothing,
            ct_IPCBANX = Nothing,
            -- Fee
            ct_FECL = Nothing,
            ct_FEANX = Nothing,
            ct_FEAC = Nothing,
            ct_FEB = Nothing,
            ct_FER = Nothing,
            ct_CURS = Nothing,
            enableSettlement = False,
            constraints = Nothing,
            collateralAmount = 0
          }
   in case genFsContract ct of
        Failure _ -> assertFailure "Terms validation should not fail"
        Success contract ->
            let principal = IDeposit (Role "counterparty") "counterparty" ada 10000
                ip = IDeposit (Role "party") "party" ada 200
                redemption = IDeposit (Role "party") "party" ada 10000

                out =
                  computeTransaction
                    ( TransactionInput
                        (0, 0)
                        [ principal,
                          ip,
                          ip,
                          ip,
                          ip,
                          ip,
                          ip,
                          ip,
                          ip,
                          ip,
                          ip,
                          redemption
                        ]
                    )
                    (emptyState 0)
                    contract
             in case out of
                  Error _ -> assertFailure "Transactions are not expected to fail"
                  TransactionOutput txWarn txPay _ con -> do
                    assertBool "Contract is in Close" $ con == Close
                    assertBool "No warnings" $ null txWarn

                    assertBool "total payments to party" (totalPayments (Party "party") txPay == 10000)
                    assertBool "total payments to counterparty" (totalPayments (Party "counterparty") txPay == 12000)

-- |example02 defines a contract of type LAM
--
-- principal: 10000
-- interest rate: 2% p.a.
-- annual interest payments
-- term: 10 years
--
-- cashflows:
-- 0 : -10000
-- 1 :   1200
-- 2 :   1180
-- 3 :   1160
-- 4 :   1140
-- 5 :   1120
-- 6 :   1100
-- 7 :   1080
-- 8 :   1060
-- 9 :   1040
-- 10:   1020
example02 :: IO ()
example02 =
  let ct =
        ContractTermsPoly
          { contractId = "0",
            contractType = LAM,
            ct_IED = iso8601ParseM "2020-01-01T00:00:00",
            ct_SD = fromJust $ iso8601ParseM "2019-12-31T00:00:00",
            ct_MD = iso8601ParseM "2030-01-01T00:00:00",
            ct_AD = Nothing,
            ct_TD = Nothing,
            ct_PRNXT = Just 1000.0,
            ct_PRD = Nothing,
            ct_CNTRL = CR_RPA,
            ct_PDIED = Nothing,
            ct_NT = Just 10000.0,
            ct_PPRD = Nothing,
            ct_PTD = Nothing,
            ct_DCC = Just DCC_E30_360,
            ct_PPEF = Just PPEF_N,
            ct_PRF = Just PRF_PF,
            scfg =
              ScheduleConfig
                { calendar = Just CLDR_NC,
                  eomc = Just EOMC_EOM,
                  bdc = Just BDC_NULL
                },
            -- Penalties
            ct_PYRT = Nothing,
            ct_PYTP = Just PYTP_O, -- no penalty
            -- Optionality
            ct_OPCL = Nothing,
            ct_OPANX = Nothing,
            -- Scaling
            ct_SCIP = Nothing,
            ct_SCIED = Nothing,
            ct_SCEF = Nothing,
            ct_SCCDD = Nothing,
            ct_SCMO = Nothing,
            ct_SCNT = Nothing,
            ct_SCCL = Nothing,
            ct_SCANX = Nothing,
            -- Rate Reset
            ct_RRCL = Nothing,
            ct_RRANX = Nothing,
            ct_RRNXT = Nothing,
            ct_RRSP = Nothing,
            ct_RRMLT = Nothing,
            ct_RRPF = Nothing,
            ct_RRPC = Nothing,
            ct_RRLC = Nothing,
            ct_RRLF = Nothing,
            ct_RRMO = Nothing,
            -- Interest
            ct_IPCED = Nothing,
            ct_IPCL = Just $ Cycle 1 P_Y ShortStub False,
            ct_IPANX = iso8601ParseM "2020-01-01T00:00:00",
            ct_IPNR = Just 0.02,
            ct_IPAC = Just 0.0,
            ct_PRCL = Just $ Cycle 1 P_Y ShortStub False,
            ct_PRANX = iso8601ParseM "2021-01-01T00:00:00",
            ct_IPCB = Just IPCB_NT,
            ct_IPCBA = Nothing,
            ct_IPCBCL = Nothing,
            ct_IPCBANX = Nothing,
            -- Fee
            ct_FECL = Nothing,
            ct_FEANX = Nothing,
            ct_FEAC = Nothing,
            ct_FEB = Nothing,
            ct_FER = Nothing,
            ct_CURS = Nothing,
            enableSettlement = False,
            constraints = Nothing,
            collateralAmount = 0
          }
   in case genFsContract ct of
        Failure _ -> assertFailure "Terms validation should not fail"
        Success contract -> do
          let principal = IDeposit (Role "counterparty") "counterparty" ada 10000
              pr i = IDeposit (Role "party") "party" ada i
              ip i = IDeposit (Role "party") "party" ada i
              out =
                computeTransaction
                  ( TransactionInput
                      (0, 0)
                      [ principal,
                        pr 1000, ip 200,
                        pr 1000, ip 180,
                        pr 1000, ip 160,
                        pr 1000, ip 140,
                        pr 1000, ip 120,
                        pr 1000, ip 100,
                        pr 1000, ip 80,
                        pr 1000, ip 60,
                        pr 1000, ip 40,
                                 ip 20,
                        pr 1000
                      ]
                  )
                  (emptyState 0)
                  contract
           in case out of
                Error _ -> assertFailure "Transactions are not expected to fail"
                TransactionOutput txWarn txPay _ con -> do
                  assertBool "Contract is in Close" $ con == Close
                  assertBool "No warnings" $ null txWarn

                  assertBool "total payments to party" (totalPayments (Party "party") txPay == 10000)
                  let tc = totalPayments (Party "counterparty") txPay
                  assertBool ("total payments to counterparty: " ++ show tc) (tc == 11100)

-- |example03 defines a contract of type NAM
--
-- principal: 10000
-- interest rate: 2% p.a.
-- annual interest payments
-- term: 10 years
--
-- cashflows:
-- 0 : -10000
-- 1 :   1000
-- 2 :   1000
-- 3 :   1000
-- 4 :   1000
-- 5 :   1000
-- 6 :   1000
-- 7 :   1000
-- 8 :   1000
-- 9 :   1000
-- 10:   2240
example03 :: IO ()
example03 =
  let ct =
        ContractTermsPoly
          { contractId = "0",
            contractType = NAM,
            ct_IED = iso8601ParseM "2020-01-01T00:00:00",
            ct_SD = fromJust $ iso8601ParseM "2019-12-31T00:00:00",
            ct_MD = iso8601ParseM "2030-01-01T00:00:00",
            ct_AD = Nothing,
            ct_TD = Nothing,
            ct_PRNXT = Just 1000.0,
            ct_PRD = Nothing,
            ct_CNTRL = CR_RPA,
            ct_PDIED = Nothing,
            ct_NT = Just 10000.0,
            ct_PPRD = Nothing,
            ct_PTD = Nothing,
            ct_DCC = Just DCC_E30_360,
            ct_PPEF = Just PPEF_N,
            ct_PRF = Just PRF_PF,
            scfg =
              ScheduleConfig
                { calendar = Just CLDR_NC,
                  eomc = Just EOMC_EOM,
                  bdc = Just BDC_NULL
                },
            -- Penalties
            ct_PYRT = Nothing,
            ct_PYTP = Just PYTP_O, -- no penalty
            -- Optionality
            ct_OPCL = Nothing,
            ct_OPANX = Nothing,
            -- Scaling
            ct_SCIP = Nothing,
            ct_SCIED = Nothing,
            ct_SCEF = Nothing,
            ct_SCCDD = Nothing,
            ct_SCMO = Nothing,
            ct_SCNT = Nothing,
            ct_SCCL = Nothing,
            ct_SCANX = Nothing,
            -- Rate Reset
            ct_RRCL = Nothing,
            ct_RRANX = Nothing,
            ct_RRNXT = Nothing,
            ct_RRSP = Nothing,
            ct_RRMLT = Nothing,
            ct_RRPF = Nothing,
            ct_RRPC = Nothing,
            ct_RRLC = Nothing,
            ct_RRLF = Nothing,
            ct_RRMO = Nothing,
            -- Interest
            ct_IPCED = Nothing,
            ct_IPCL = Just $ Cycle 1 P_Y ShortStub False,
            ct_IPANX = iso8601ParseM "2020-01-01T00:00:00",
            ct_IPNR = Just 0.02,
            ct_IPAC = Just 0.0,
            ct_PRCL = Just $ Cycle 1 P_Y ShortStub False,
            ct_PRANX = iso8601ParseM "2021-01-01T00:00:00",
            ct_IPCB = Just IPCB_NT,
            ct_IPCBA = Just 1000,
            ct_IPCBCL = Just $ Cycle 1 P_Y ShortStub False,
            ct_IPCBANX = iso8601ParseM "2021-01-01T00:00:00",
            -- Fee
            ct_FECL = Nothing,
            ct_FEANX = Nothing,
            ct_FEAC = Nothing,
            ct_FEB = Nothing,
            ct_FER = Nothing,
            ct_CURS = Nothing,
            enableSettlement = False,
            constraints = Nothing,
            collateralAmount = 0
          }
   in case genFsContract ct of
        Failure _ -> assertFailure "Terms validation should not fail"
        Success contract -> do
          let principal = IDeposit (Role "counterparty") "counterparty" ada 10000
              pr i = IDeposit (Role "party") "party" ada i
              ip i = IDeposit (Role "party") "party" ada i
              out =
                computeTransaction
                  ( TransactionInput
                      (0, 0)
                      [ principal,
                        pr 800, ip 200,
                        pr 816, ip 184,
                        pr 832, ip 168,
                        pr 849, ip 151,
                        pr 866, ip 134,
                        pr 883, ip 117,
                        pr 901, ip 99,
                        pr 919, ip 81,
                        pr 937, ip 63,
                                ip 44,
                        pr 2196
                      ]
                  )
                  (emptyState 0)
                  contract
           in case out of
                Error _ -> assertFailure "Transactions are not expected to fail"
                TransactionOutput txWarn txPay _ con -> do
                  assertBool "Contract is in Close" $ con == Close
                  assertBool "No warnings" $ null txWarn

                  assertBool "total payments to party" (totalPayments (Party "party") txPay == 10000)
                  let tc = totalPayments (Party "counterparty") txPay
                  assertBool ("total payments to counterparty: " ++ show tc) (tc == 11240)

-- |example04 defines a contract of type ANN
--
-- principal: 10000
-- interest rate: 2% p.a.
-- annual interest payments
-- term: 10 years
--
-- cashflows:
-- 0 : -10000
-- 1 :   1000
-- 2 :   1000
-- 3 :   1000
-- 4 :   1000
-- 5 :   1000
-- 6 :   1000
-- 7 :   1000
-- 8 :   1000
-- 9 :   1000
-- 10:   2240
example04 :: IO ()
example04 =
  let ct =
        ContractTermsPoly
          { contractId = "0",
            contractType = ANN,
            ct_IED = iso8601ParseM "2020-01-01T00:00:00",
            ct_SD = fromJust $ iso8601ParseM "2019-12-31T00:00:00",
            ct_MD = iso8601ParseM "2030-01-01T00:00:00",
            ct_AD = Nothing,
            ct_TD = Nothing,
            ct_PRNXT = Just 1000,
            ct_PRD = Nothing,
            ct_CNTRL = CR_RPA,
            ct_PDIED = Nothing,
            ct_NT = Just 10000.0,
            ct_PPRD = Nothing,
            ct_PTD = Nothing,
            ct_DCC = Just DCC_E30_360,
            ct_PPEF = Just PPEF_N,
            ct_PRF = Just PRF_PF,
            scfg =
              ScheduleConfig
                { calendar = Just CLDR_NC,
                  eomc = Just EOMC_EOM,
                  bdc = Just BDC_NULL
                },
            -- Penalties
            ct_PYRT = Nothing,
            ct_PYTP = Just PYTP_O, -- no penalty
            -- Optionality
            ct_OPCL = Nothing,
            ct_OPANX = Nothing,
            -- Scaling
            ct_SCIP = Nothing,
            ct_SCIED = Nothing,
            ct_SCEF = Nothing,
            ct_SCCDD = Nothing,
            ct_SCMO = Nothing,
            ct_SCNT = Nothing,
            ct_SCCL = Nothing,
            ct_SCANX = Nothing,
            -- Rate Reset
            ct_RRCL = Nothing,
            ct_RRANX = Nothing,
            ct_RRNXT = Nothing,
            ct_RRSP = Nothing,
            ct_RRMLT = Nothing,
            ct_RRPF = Nothing,
            ct_RRPC = Nothing,
            ct_RRLC = Nothing,
            ct_RRLF = Nothing,
            ct_RRMO = Nothing,
            -- Interest
            ct_IPCED = Nothing,
            ct_IPCL = Just $ Cycle 1 P_Y ShortStub False,
            ct_IPANX = iso8601ParseM "2020-01-01T00:00:00",
            ct_IPNR = Just 0.02,
            ct_IPAC = Just 0.0,
            ct_PRCL = Just $ Cycle 1 P_Y ShortStub False,
            ct_PRANX = iso8601ParseM "2021-01-01T00:00:00",
            ct_IPCB = Just IPCB_NT,
            ct_IPCBA = Nothing,
            ct_IPCBCL = Nothing,
            ct_IPCBANX = Nothing,
            -- Fee
            ct_FECL = Nothing,
            ct_FEANX = Nothing,
            ct_FEAC = Nothing,
            ct_FEB = Nothing,
            ct_FER = Nothing,
            ct_CURS = Nothing,
            enableSettlement = False,
            constraints = Nothing,
            collateralAmount = 0
          }
   in case genFsContract ct of
        Failure _ -> assertFailure "Terms validation should not fail"
        Success contract -> do
          let principal = IDeposit (Role "counterparty") "counterparty" ada 10000
              pr i = IDeposit (Role "party") "party" ada i
              ip i = IDeposit (Role "party") "party" ada i
              out =
                computeTransaction
                  ( TransactionInput
                      (0, 0)
                      [ principal,
                        pr 800, ip 200,
                        pr 816, ip 184,
                        pr 832, ip 168,
                        pr 849, ip 151,
                        pr 866, ip 134,
                        pr 883, ip 117,
                        pr 901, ip 99,
                        pr 919, ip 81,
                        pr 937, ip 63,
                                ip 44,
                        pr 2196
                      ]
                  )
                  (emptyState 0)
                  contract
           in case out of
                Error _ -> assertFailure "Transactions are not expected to fail"
                TransactionOutput txWarn txPay _ con -> do
                  assertBool "Contract is in Close" $ con == Close
                  assertBool "No warnings" $ null txWarn

                  assertBool "total payments to party" (totalPayments (Party "party") txPay == 10000)
                  let tc = totalPayments (Party "counterparty") txPay
                  assertBool ("total payments to counterparty: " ++ show tc) (tc == 11240)

-- |totalPayments calculates the sum of the payments provided as argument
totalPayments :: Payee -> [Payment] -> Integer
totalPayments payee = sum . map m . filter f
  where
    m (Payment _ _ mon) = Val.valueOf mon "" ""
    f (Payment _ pay _) = pay == payee
