module Spec.Marlowe.Actus
    ( tests
    )
where

import           Language.Marlowe.ACTUS.Control
import           Language.Marlowe.ACTUS.ControlLp
import           Language.Marlowe.Semantics
import           Language.Marlowe.Pretty
import           Language.Marlowe.ACTUS.ContractTerms
import           Language.Marlowe.ACTUS.ContractState
import           Language.Marlowe.ACTUS.BusinessEvents
import           Language.Marlowe.ACTUS.ActusValidator
import           Language.Marlowe.ACTUS.Schedule
import           Language.Marlowe.ACTUS.ProjectedCashFlows
import           Test.Tasty
import           Test.Tasty.HUnit
import           Data.Time
import           Data.String (IsString (fromString))
import           Ledger.Value
import           Ledger.Ada                 (adaSymbol, adaToken)

tests :: TestTree
tests = testGroup "Actus"
    [ testCase "PAM static schedule" pamProjected
    , testCase "PAM static contract" pamStatic
    , testCase "Simple PAM contract + Marlowe IO" pamSimple
    , testCase "Simple PAM contract" pamRePlay
    , testCase "Generate PAM-LP" pamLpGeneration

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
        , _CNTRL = CR_LG
        , _PDIED = -100.0 -- Discount At IED
        , _NT = 1000.0 -- Notional
        , _PPRD = 1200.0 -- Price At Purchase Date
        , _PTD = 1200.0 -- Price At Termination Date
        , _DCC = DCC_A_360 -- Date Count Convention
        , _PREF = PREF_Y -- allow PP
        , _PRF = CS_PF
        , scfg = ScheduleConfig {
            calendar = const True
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


pamRePlay :: IO ()
pamRePlay = do 
    let cf1 = cashFlowFixture 0 (_SD contractTerms) (projectEvent IED) 900.0
    let cf2 = cashFlowFixture 1 (_MD contractTerms) (projectEvent MD) 1000.0
    let result = validateCashFlow contractTerms [cf1] cf2
    assertBool "Result" result


pamSimple :: IO ()
pamSimple = do
    let customValidator = actusMarloweValidator contractTerms
    let contract = genContract
    let initState = emptyState 0
    let inputs = 
            let 
                mkChoice role choice = 
                    IChoice $ ChoiceId (fromString choice) (Role $ TokenName $ fromString role)
                mkDeposit role = 
                    IDeposit (AccountId 0 $ Role $ TokenName $ fromString role) (Role $ TokenName $ fromString role) ada
                chooseContractId = mkChoice "party" "contractId" 10
                chooseEventType = mkChoice "party" "eventType" (eventTypeToEventTypeId AD)
                chooseRiskFactor1 = mkChoice "oracle" "riskFactor-o_rf_CURS" 0
                chooseRiskFactor2 = mkChoice "oracle" "riskFactor-o_rf_RRMO" 0
                chooseRiskFactor3 = mkChoice "oracle" "riskFactor-o_rf_SCMO" 0
                chooseRiskFactor4 = mkChoice "oracle" "riskFactor-pp_payoff" 0
                choosePayoff = mkChoice "party" "payoff" 0
                choosePayoffCurrency = mkChoice "party" "payoffCurrency" 0
                doDeposit = mkDeposit "party" 0
            in [chooseContractId, chooseEventType, chooseRiskFactor1, chooseRiskFactor2, chooseRiskFactor3,
                chooseRiskFactor4, choosePayoff, choosePayoffCurrency, doDeposit]
        --
    let txInput = TransactionInput { txInterval = (0, 2000), txInputs = inputs }
    let txOutput = computeTransactionWithLoopSupport txInput initState contract
    let validationResult = customValidator txOutput --trace ("\ntxout: " ++ (show txOutput) ++ "\ncontract = " ++ (show contract)) $ 
    let parsedCashFlows = stateParser $ (appendPresentState $ txOutState txOutput)
    let parsedCashFlowsEmpty = null parsedCashFlows
    assertBool "Parsed cashflows are not empty" $ not parsedCashFlowsEmpty
    assertBool "Validation result" validationResult
    assertEqual "Contract is closed" Close (txOutContract txOutput)

pamLpGeneration :: IO ()
pamLpGeneration = do
    let pamLp = genLpContract contractTerms 1 Close
    -- print $ pretty pamLp
    assertBool "Contract Generated" $ pamLp /= Close

