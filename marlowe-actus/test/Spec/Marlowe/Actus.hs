module Spec.Marlowe.Actus
    ( tests
    )
where

import           Data.Aeson                                       (decode, encode)
import           Data.ByteString.Lazy.Char8                       (unpack)
import           Data.Time
import           Data.Validation                                  (Validation (..))
import           Language.Marlowe.ACTUS.Analysis
import           Language.Marlowe.ACTUS.Definitions.ContractTerms
import           Language.Marlowe.ACTUS.Generator
import           Language.Marlowe.Pretty
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
        , contractType = Just PAM
        , ct_IED = fromGregorian 2020 10 20 -- Initial Exchange Date
        , ct_SD = fromGregorian 2007 10 22 -- status date
        , ct_MD = Just $ fromGregorian 2025 10 22 -- maturity date
        , ct_TD = Nothing  -- termination date
        , ct_PRNXT = Nothing -- Next principal redemption payment (N/A for PAM)
        , ct_PRD = Nothing -- purchase date
        , ct_CNTRL = CR_BUY
        , ct_PDIED = -100.0 -- Discount At IED
        , ct_NT = Just 1000.0 -- Notional
        , ct_PPRD = Nothing-- Price At Purchase Date
        , ct_PTD = Nothing -- Price At Termination Date
        , ct_DCC = DCC_A_360 -- Date Count Convention
        , ct_PREF = PREF_Y -- allow PP
        , ct_PRF = CS_PF
        , scfg = ScheduleConfig {
            calendar = []
            , includeEndDay = False
            , eomc = EOMC_EOM
            , bdc = BDC_NULL
        }
        -- Penalties
        , ct_PYRT = 0.0
        , ct_PYTP = PYTP_A -- Penalty Pype
        , ct_cPYRT = 0.0
        -- Optionality
        , ct_OPCL = Nothing
        , ct_OPANX = Nothing
        -- Scaling:
        , ct_SCIED = 0.0
        , ct_SCEF = SE_000
        , ct_SCCL = Nothing
        , ct_SCANX = Nothing
        , ct_SCIXSD = 0.0
        -- Rate Reset
        , ct_RRCL = Nothing
        , ct_RRANX = Nothing
        , ct_RRNXT = Nothing
        , ct_RRSP = 0.0
        , ct_RRMLT = 0.0
        , ct_RRPF = 0.0
        , ct_RRPC = 0.0
        , ct_RRLC = 0.0
        , ct_RRLF = 0.0
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
        , ct_FECL  = Nothing
        , ct_FEANX  = Nothing
        , ct_FEAC  = Nothing
        , ct_FEB = FEB_N
        , ct_FER = 0.03 -- fee rate
        , ct_CURS = False
        , constraints = Nothing
        , collateralAmount = 10000
    }

namContractTerms :: ContractTerms
namContractTerms =
  contractTerms{
    contractType = Just NAM,
    ct_SD = fromGregorian 2015 1 1,
    ct_CNTRL = CR_RPA,
    ct_IPANX = Just $ fromGregorian 2016 1 2,
    ct_IPCL = Just $ Cycle 1 P_Y ShortStub,
    ct_IPNR = Just 0.05,
    ct_IPCB = Just IPCB_NT,
    ct_IED = fromGregorian 2015 1 2,
    ct_PRANX = Just $ fromGregorian 2016 1 2,
    ct_PRCL = Just $ Cycle 1 P_Y ShortStub,
    ct_PRNXT = Just 200.0,
    ct_RRCL = Just $ Cycle 1 P_Y ShortStub,
    ct_RRSP = 0.02,
    ct_FER = 0.0,
    collateralAmount = 0
    }

pamProjected :: IO ()
pamProjected = do
    let cfs = genProjectedCashflows contractTerms
    let cfsEmpty = null cfs
    assertBool "Cashflows should not be empty" (not cfsEmpty)

pamStatic :: IO ()
pamStatic = case genStaticContract contractTerms of
  Failure f ->
    do
      print f
      assertFailure "Terms validation should not fail"
  Success contract ->
    do
      assertBool "Cashflows should not be Close" $ contract /= Close

pamFs :: IO ()
pamFs = do
    let jsonTermsStr = encode contractTerms
    writeFile "ContractTerms.json" $ unpack jsonTermsStr
    let jsonTerms' = decode jsonTermsStr :: Maybe ContractTerms
    assertBool "JSON terms there and back" $ not $ null jsonTerms'
    case genFsContract contractTerms of
      Failure _ -> assertFailure "Terms validation should not fail"
      Success contract -> do
        writeFile "PamFs.marlowe" $ show $ pretty contract
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
    do
      assertBool "Cashflows should not be Close" $ contract /= Close

namFs :: IO ()
namFs = do
    let jsonTermsStr = encode namContractTerms
    writeFile "ContractTerms.json" $ unpack jsonTermsStr
    let jsonTerms' = decode jsonTermsStr :: Maybe ContractTerms
    assertBool "JSON terms there and back" $ not $ null jsonTerms'
    case genFsContract namContractTerms of
      Failure _ -> assertFailure "Terms validation should not fail"
      Success contract -> do
        writeFile "NamFs.marlowe" $ show $ pretty contract
        assertBool "Cashflows should not be Close" $ contract /= Close
