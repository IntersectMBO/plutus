module Spec.Marlowe.Actus
    ( tests
    )
where

import           Language.Marlowe.ACTUS.Control
import           Language.Marlowe.Semantics
import           Language.Marlowe.ACTUS.ContractTerms
import           Language.Marlowe.ACTUS.ContractState
import           Language.Marlowe.ACTUS.BusinessEvents
import           Test.Tasty
import           Test.Tasty.HUnit
import           Data.Time
import           Data.Maybe
import           Language.Marlowe.Client
import           Data.String (IsString (fromString))
import           Ledger.Crypto
import           Ledger.Value
import           Debug.Trace

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
    let customValidator = actusMarloweValidator contractTerms
    let contract = genContract
    let initState = emptyState 0
    let inputs = (let 
                mkChoice role choice value = 
                    IChoice (ChoiceId (fromString choice) (Role $ TokenName $ fromString role)) value
                chooseContractId = mkChoice "party" "contractId" 10
                chooseEventType = mkChoice "party" "eventType" (eventTypeToEventTypeId IP)
                chooseRiskFactor1 = mkChoice "oracle" "riskFactor-o_rf_CURS" 0
                chooseRiskFactor2 = mkChoice "oracle" "riskFactor-o_rf_RRMO" 0
                chooseRiskFactor3 = mkChoice "oracle" "riskFactor-o_rf_SCMO" 0
                chooseRiskFactor4 = mkChoice "oracle" "riskFactor-pp_payoff" 0
                choosePayoff = mkChoice "party" "payoff" 0
                choosePayoffCurrency = mkChoice "party" "payoffCurrency" 0
                in [chooseContractId, chooseEventType, chooseRiskFactor1, chooseRiskFactor2, chooseRiskFactor3,
                chooseRiskFactor4, choosePayoff, choosePayoffCurrency])
        --(IDeposit AccountId Party ada 100)
    let txInput = TransactionInput { txInterval = (0, 2000), txInputs = inputs }
    let txOutput = computeTransactionWithLoopSupport txInput initState contract
    let validationResult = trace ("\ntxout: " ++ (show txOutput) ++ "\ncontract = " ++ (show contract)) $ customValidator txOutput
    let parsedCashFlows = stateParser $ txOutState txOutput
    let parsedCashFlowsEmpty = null parsedCashFlows
    assertBool "Result" validationResult
    assertBool "ParsedCashflows are empty" $ not parsedCashFlowsEmpty
    assertEqual "Contract is not closed" Close (txOutContract txOutput)

