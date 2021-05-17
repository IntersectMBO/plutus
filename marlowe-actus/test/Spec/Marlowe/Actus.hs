module Spec.Marlowe.Actus
    ( tests
    )
where

import           Data.Aeson                                       (decode, encode)
import           Data.Time
import           Data.Validation                                  (Validation (..))
import           Language.Marlowe.ACTUS.Analysis
import           Language.Marlowe.ACTUS.Definitions.ContractTerms
import           Language.Marlowe.ACTUS.Generator
import           Language.Marlowe.Semantics
import           Test.Tasty
import           Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "Actus"
    [ testCase "PAM static schedule" pamProjected
    , testCase "PAM static contract" pamStatic
    , testCase "PAM fixed schedule contract" pamFs
    , testCase "NAM static schedule" namProjected
    , testCase "NAM static contract" namStatic
    , testCase "NAM fixed schedule contract" namFs
    ]

contractTerms :: ContractTerms
contractTerms = ContractTerms {
          contractId = "0"
        , contractType = PAM
        , ct_IED = Just $ fromGregorian 2020 10 20 -- Initial Exchange Date
        , ct_SD = fromGregorian 2007 10 22 -- status date
        , ct_MD = Just $ fromGregorian 2025 10 22 -- maturity date
        , ct_TD = Nothing  -- termination date
        , ct_PRNXT = Nothing -- Next principal redemption payment (N/A for PAM)
        , ct_PRD = Nothing -- purchase date
        , ct_CNTRL = CR_BUY
        , ct_PDIED = Just $ -100.0 -- Discount At IED
        , ct_NT = Just 1000.0 -- Notional
        , ct_PPRD = Nothing-- Price At Purchase Date
        , ct_PTD = Nothing -- Price At Termination Date
        , ct_DCC = Just DCC_A_360 -- Date Count Convention
        , ct_PPEF = Just PPEF_A -- allow PP
        , ct_PRF = Just PRF_PF
        , scfg = ScheduleConfig {
            calendar = []
            , includeEndDay = False
            , eomc = Just EOMC_EOM
            , bdc = Just BDC_NULL
        }
        -- Penalties
        , ct_PYRT = Just 0.0
        , ct_PYTP = Just PYTP_A -- Penalty Pype
        , ct_cPYRT = 0.0
        -- Optionality
        , ct_OPCL = Nothing
        , ct_OPANX = Nothing
        -- Scaling:
        , ct_SCIED = Nothing
        , ct_SCEF = Nothing
        , ct_SCCL = Nothing
        , ct_SCANX = Nothing
        , ct_SCIXSD = 0.0
        -- Rate Reset
        , ct_RRCL = Nothing
        , ct_RRANX = Nothing
        , ct_RRNXT = Nothing
        , ct_RRSP = Nothing
        , ct_RRMLT = Nothing
        , ct_RRPF = Nothing
        , ct_RRPC = Nothing
        , ct_RRLC = Nothing
        , ct_RRLF = Nothing
        -- Interest
        , ct_IPCED = Nothing
        , ct_IPCL  = Just $ Cycle 1 P_Y ShortStub
        , ct_IPANX = Just $ fromGregorian 2021 10 20
        , ct_IPNR  = Just 0.1
        , ct_IPAC  = Nothing
        , ct_PRCL = Nothing
        , ct_PRANX = Nothing
        , ct_IPCB = Nothing   -- Interest calc base
        , ct_IPCBA = Nothing -- Amount used for interest calculation
        , ct_IPCBCL = Nothing  -- Cycle of interest calculation base
        , ct_IPCBANX = Nothing   -- Anchor of interest calc base cycle
        -- Fee
        , ct_FECL  = Just $ Cycle 1 P_Y ShortStub
        , ct_FEANX  = Nothing
        , ct_FEAC  = Nothing
        , ct_FEB = Just FEB_N
        , ct_FER = Just 0.03 -- fee rate
        , ct_CURS = False
        , constraints = Nothing
        , collateralAmount = 10000
    }

namContractTerms :: ContractTerms
namContractTerms =
  contractTerms{
    contractType = NAM,
    ct_SD = fromGregorian 2015 1 1,
    ct_CNTRL = CR_RPA,
    ct_IPANX = Just $ fromGregorian 2016 1 2,
    ct_IPCL = Just $ Cycle 1 P_Y ShortStub,
    ct_IPNR = Just 0.05,
    ct_IPCB = Just IPCB_NT,
    ct_IED = Just $ fromGregorian 2015 1 2,
    ct_PRANX = Just $ fromGregorian 2016 1 2,
    ct_PRCL = Just $ Cycle 1 P_Y ShortStub,
    ct_PRNXT = Just 200.0,
    ct_RRCL = Just $ Cycle 1 P_Y ShortStub,
    ct_RRSP = Just 0.02,
    ct_FER = Just 0.0,
    collateralAmount = 0
    }

pamProjected :: IO ()
pamProjected = do
    let cfs = genProjectedCashflows contractTerms
    let cfsEmpty = null cfs
    assertBool "Cashflows should not be empty" (not cfsEmpty)

pamStatic :: IO ()
pamStatic = case genStaticContract contractTerms of
  Failure _        -> assertFailure "Terms validation should not fail"
  Success contract ->
    assertBool "Cashflows should not be Close" $ contract /= Close

pamFs :: IO ()
pamFs = do
    let jsonTermsStr = encode contractTerms
    let jsonTerms' = decode jsonTermsStr :: Maybe ContractTerms
    assertBool "JSON terms there and back" $ not $ null jsonTerms'
    case genFsContract contractTerms of
      Failure _ ->
        assertFailure "Terms validation should not fail"
      Success contract ->
        assertBool "Cashflows should not be Close" $ contract /= Close

namProjected :: IO ()
namProjected = do
    let cfs = genProjectedCashflows namContractTerms
    let cfsEmpty = null cfs
    assertBool "Cashflows should not be empty" (not cfsEmpty)

namStatic :: IO ()
namStatic = case genStaticContract namContractTerms of
  Failure _ -> assertFailure "Terms validation should not fail"
  Success contract ->
      assertBool "Cashflows should not be Close" $ contract /= Close

namFs :: IO ()
namFs = do
    let jsonTermsStr = encode namContractTerms
    let jsonTerms' = decode jsonTermsStr :: Maybe ContractTerms
    assertBool "JSON terms there and back" $ not $ null jsonTerms'
    case genFsContract namContractTerms of
      Failure _ -> assertFailure "Terms validation should not fail"
      Success contract ->
        assertBool "Cashflows should not be Close" $ contract /= Close
