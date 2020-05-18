module Spec.Marlowe.Actus
    ( tests
    )
where

import           Language.Marlowe.ACTUS.Control
import           Language.Marlowe.Semantics
import           Language.Marlowe.ACTUS.ContractTerms
import           Language.Marlowe.ACTUS.ContractState
import           Test.Tasty
import           Test.Tasty.HUnit
import           Data.Time
import           Data.Maybe


tests :: TestTree
tests = testGroup "Actus"
    [ testCase "Simple PAM contract" pamSimple
    ]

pamSimple :: IO ()
pamSimple = do
    let contractTerms = PamContractTerms {
            contractId = ""
        , _SD = fromGregorian 2008 10 22 -- start date
        , _MD = fromGregorian 2009 10 22 -- maturity date
        , _TD = fromGregorian 2009 10 22  -- termination date
        , _PRD = fromGregorian 2009 10 22 -- purchase date
        , _IED = fromGregorian 2009 10 22 -- Initial Exchange Date
        , _CNTRL = CR_LG
        , _PDIED = 100.0 -- Premium Discount At IED
        , _NT = 1000.0 -- Notional
        , _PPRD = 1200.0 -- Price At Purchase Date
        , _PTD = 1200.0 -- Price At Termination Date
        , _DCC = DCC_A_360 -- Date Count Convention
        , _PREF = PREF_Y -- allow PP
        , _PRF = CS_PF
        , scfg = ScheduleConfig {
            calendar = (\_ -> True)
            , includeEndDay = False
            , eomc = EOMC_EOM
            , bdc = BDC_NULL
        }
        -- Penalties
        , _PYRT = 0.0
        , _PYTP = PYTP_A -- Penalty Pype
        , _cPYRT = 0.0
        -- Optionality
        , _OPCL = Nothing
        , _OPANX = Nothing
        -- Scaling:
        , _SCIED = 0.0
        , _SCEF = SE_000
        , _SCCL = Nothing
        , _SCANX = Nothing
        , _SCIXSD = 0.0
        -- Rate Reset
        , _RRCL = Nothing
        , _RRANX = Nothing
        , _RRNXT = Nothing 
        , _RRSP = 0.0
        , _RRMLT = 0.0
        , _RRPF = 0.0
        , _RRPC = 0.0
        , _RRLC = 0.0
        , _RRLF = 0.0
        -- Interest
        , _IPCED = Nothing
        , _IPCL  = Nothing
        , _IPANX = Nothing
        , _IPNR  = Nothing
        , _IPAC  = Nothing
        -- Fee
        , _FECL  = Nothing
        , _FEANX  = Nothing
        , _FEAC  = Nothing
        , _FEB = FEB_N
        , _FER = 0.03 -- fee rate
    }
    assertBool  "Result" True
