module Spec.Marlowe.Actus
    ( tests
    )
where

import           Data.Aeson                                       (decode, encode)
import           Data.ByteString.Lazy.Char8                       (unpack)
import           Data.Time
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
    ]

contractTerms :: ContractTerms
contractTerms = ContractTerms {
          contractId = "0"
        , contractType = PAM
        , ct_IED = fromGregorian 2008 10 20 -- Initial Exchange Date
        , ct_SD = fromGregorian 2008 10 22 -- start date
        , ct_MD = fromGregorian 2009 10 22 -- maturity date
        , ct_TD = fromGregorian 2009 10 22  -- termination date
        , ct_PRD = fromGregorian 2008 10 20 -- purchase date
        , ct_CNTRL = CR_ST
        , ct_PDIED = -100.0 -- Discount At IED
        , ct_NT = 1000.0 -- Notional
        , ct_PPRD = 1200.0 -- Price At Purchase Date
        , ct_PTD = 1200.0 -- Price At Termination Date
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
        , ct_IPCL  = Nothing
        , ct_IPANX = Nothing
        , ct_IPNR  = Nothing
        , ct_IPAC  = Nothing
        -- Fee
        , ct_FECL  = Nothing
        , ct_FEANX  = Nothing
        , ct_FEAC  = Nothing
        , ct_FEB = FEB_N
        , ct_FER = 0.03 -- fee rate
        , ct_CURS = False
        , constraints = Nothing
    }

pamProjected :: IO ()
pamProjected = do
    let cfs = genProjectedCashflows contractTerms
    let cfsEmpty = null cfs
    assertBool "Cashflows should not be empty" (not cfsEmpty)

pamStatic :: IO ()
pamStatic = do
    let contract = genStaticContract contractTerms
    assertBool "Cashflows should not be Close" $ contract /= Close

pamFs :: IO ()
pamFs = do
    let jsonTermsStr = encode contractTerms
    writeFile "ContractTerms.json" $ unpack jsonTermsStr
    let jsonTerms' = decode jsonTermsStr :: Maybe ContractTerms
    assertBool "JSON terms there and back" $ not $ null jsonTerms'
    let contract = genFsContract contractTerms
    writeFile "PamFs.marlowe" $ show $ pretty contract
    assertBool "Cashflows should not be Close" $ contract /= Close


