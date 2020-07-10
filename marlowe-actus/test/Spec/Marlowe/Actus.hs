module Spec.Marlowe.Actus
    ( tests
    )
where

import           Language.Marlowe.ACTUS.Generator
import           Language.Marlowe.Semantics
import           Language.Marlowe.Pretty
import           Language.Marlowe.ACTUS.Definitions.ContractTerms
import           Language.Marlowe.ACTUS.Definitions.ContractState
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents
import           Language.Marlowe.ACTUS.Definitions.Schedule
import           Language.Marlowe.Analysis.FSSemantics
import           Test.Tasty
import           Test.Tasty.HUnit
import           Data.Time
import           Data.Either
import           Data.String (IsString (fromString))
import           Ledger.Value
import           Ledger.Ada                 (adaSymbol, adaToken)
import           System.IO (writeFile)

tests :: TestTree
tests = testGroup "Actus"
    [ testCase "PAM static schedule" pamProjected
    , testCase "PAM static contract" pamStatic
    , testCase "PAM fixed schedule contract" pamFs
    ]

ada :: Token
ada = Token adaSymbol adaToken

contractTerms :: ContractTerms
contractTerms = ContractTerms {
          contractId = "0"
        , contractType = PAM
        , _IED = fromGregorian 2008 10 20 -- Initial Exchange Date
        , _SD = fromGregorian 2008 10 22 -- start date
        , _MD = fromGregorian 2009 10 22 -- maturity date
        , _TD = fromGregorian 2009 10 22  -- termination date
        , _PRD = fromGregorian 2008 10 20 -- purchase date
        , _CNTRL = CR_ST
        , _PDIED = -100.0 -- Discount At IED
        , _NT = 1000.0 -- Notional
        , _PPRD = 1200.0 -- Price At Purchase Date
        , _PTD = 1200.0 -- Price At Termination Date
        , _DCC = DCC_A_360 -- Date Count Convention
        , _PREF = PREF_Y -- allow PP
        , _PRF = CS_PF
        , scfg = ScheduleConfig {
            calendar = []
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

cashFlowFixture :: Integer -> Day -> ScheduledEvent -> Double -> CashFlow
cashFlowFixture t date event amnt = CashFlow {
    tick = t,
    cashContractId = "0",
    cashParty = "party",
    cashCounterParty = "counterparty",
    cashPaymentDay = date,
    cashCalculationDay = date,
    cashEvent = event,
    amount = amnt,
    currency = "ada"
}

pamProjected :: IO ()
pamProjected = do 
    let cfs = genProjectedCashflows contractTerms 
    let cfsEmpty = null cfs
    assertBool "Cashflows should not be empty" (not cfsEmpty) --trace ("Projected CashFlows: " ++ (show cfs))
    return ()

pamStatic :: IO ()
pamStatic = do 
    let contract = genStaticContract contractTerms 
    --print $ pretty contract
    assertBool "Cashflows should not be Close" $ contract /= Close --trace ("Projected CashFlows: " ++ (show cfs))
    return ()

pamFs :: IO ()
pamFs = do 
    let contract = genFsContract contractTerms 
    writeFile "PamFs.hs" $ show $ pretty contract
    assertBool "Cashflows should not be Close" $ contract /= Close --trace ("Projected CashFlows: " ++ (show cfs))
    return ()

