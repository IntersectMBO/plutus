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
    , testCase "Simple PAM contract + Marlowe IO" pamSimple
    , testCase "Simple PAM contract" pamRePlay
   --, testCase "Generate PAM-LP" pamLpGeneration
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

pamFs :: IO ()
pamFs = do 
    let contract = genFsContract contractTerms 
    writeFile "PamFs.hs" $ show $ pretty contract
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
        contract = genContract
        initState = emptyState 0
        mkChoice role choice = 
            IChoice $ ChoiceId (fromString choice) (Role $ TokenName $ fromString role)
        mkDeposit role = 
            IDeposit (AccountId 0 $ Role $ TokenName $ fromString role) (Role $ TokenName $ fromString role) ada
    let inputs1 = 
                [   mkChoice "party" "contractId" 10
                ,   mkChoice "party" "eventType" (eventTypeToEventTypeId AD)
                ,   mkChoice "oracle" "riskFactor-o_rf_CURS" 0
                ,   mkChoice "oracle" "riskFactor-o_rf_RRMO" 0
                ,   mkChoice "oracle" "riskFactor-o_rf_SCMO" 0
                ,   mkChoice "oracle" "riskFactor-pp_payoff" 0
                ,   mkChoice "party" "payoff" 0
                ,   mkChoice "party" "payoffCurrency" 0
                ,   mkDeposit "party" 0
                ]
    let inputs2 =
                [   mkChoice "party" "contractId" 10
                ,   mkChoice "party" "eventType" (eventTypeToEventTypeId IED)
                ,   mkChoice "oracle" "riskFactor-o_rf_CURS" $ round marloweFixedPoint 
                ,   mkChoice "oracle" "riskFactor-o_rf_RRMO" 0
                ,   mkChoice "oracle" "riskFactor-o_rf_SCMO" 0
                ,   mkChoice "oracle" "riskFactor-pp_payoff" 0
                ,   mkChoice "party" "payoff" 900
                ,   mkChoice "party" "payoffCurrency" 0
                ,   mkDeposit "party" 900
                ]
    let txInput1 = TransactionInput { txInterval = (0, 2000), txInputs = inputs1 }
    let txOutput1 = computeTransactionWithLoopSupport txInput1 initState contract
    let validationResult1 = customValidator txOutput1 --trace ("\ntxout: " ++ (show txOutput) ++ "\ncontract = " ++ (show contract)) $ 
    let state1 = txOutState txOutput1 

    let txInput2 = TransactionInput { txInterval = (0, 2000), txInputs = inputs2 }
    let txOutput2 = computeTransactionWithLoopSupport txInput2 state1 contract
    let validationResult2 = customValidator txOutput2 --trace ("\ntxout: " ++ (show txOutput) ++ "\ncontract = " ++ (show contract)) $ 
       
    
    let parsedCashFlows = stateParser $ appendPresentState $ txOutState txOutput1
    let parsedCashFlowsEmpty = null parsedCashFlows
    assertBool "Parsed cashflows are not empty" $ not parsedCashFlowsEmpty
    assertBool "Validation result" validationResult1
    assertEqual "Contract is closed" Close (txOutContract txOutput1)
    assertBool "Validation result 2" validationResult2
    assertEqual "Contract is closed 2" Close (txOutContract txOutput2)

pamLpGeneration :: IO ()
pamLpGeneration = do
    let pamLp = foldl (flip $ genLpContract contractTerms) Close [1 .. 5]
    --print $ pretty pamLp
    analysisResult <- warningsTrace pamLp
    --print analysisResult
    assertBool "Contract Generated" $ pamLp /= Close
    assertBool "Static analysis" $ isRight analysisResult


