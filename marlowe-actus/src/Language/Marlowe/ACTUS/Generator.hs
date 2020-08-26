{-# LANGUAGE RecordWildCards #-}

{- This module contains templates for Marlowe constructs required by ACTUS logic -}
module Language.Marlowe.ACTUS.Generator
    (
    genStaticContract
    , genFsContract
    , genProjectedCashflows
    )
where

import qualified Data.List                                               as L (scanl, tail, zip, zip5)
import           Data.Maybe                                              (fromMaybe)
import           Data.String                                             (IsString (fromString))
import           Data.Time                                               (fromGregorian)
import           Language.Marlowe                                        (AccountId (AccountId),
                                                                          Action (Choice, Deposit), Bound (Bound),
                                                                          Case (Case), ChoiceId (ChoiceId),
                                                                          Contract (Close, Let, Pay, When), Observation,
                                                                          Party (Role), Payee (Party), Slot (..),
                                                                          Value (ChoiceValue, Constant, NegValue, UseValue),
                                                                          ValueId (ValueId), ada)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents       (EventType (..), RiskFactors (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms        (ContractTerms)
import           Language.Marlowe.ACTUS.Definitions.Schedule             (CashFlow (..), ShiftedDay (..),
                                                                          calculationDay, paymentDay)
import           Language.Marlowe.ACTUS.MarloweCompat                    (dayToSlotNumber)
import           Language.Marlowe.ACTUS.Model.INIT.StateInitialization   (inititializeState)
import           Language.Marlowe.ACTUS.Model.INIT.StateInitializationFs (inititializeStateFs)
import           Language.Marlowe.ACTUS.Model.POF.Payoff                 (payoff)
import           Language.Marlowe.ACTUS.Model.POF.PayoffFs               (payoffFs)
import           Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule     (schedule)
import           Language.Marlowe.ACTUS.Model.STF.StateTransition        (stateTransition)
import           Language.Marlowe.ACTUS.Model.STF.StateTransitionFs      (stateTransitionFs)
import           Ledger.Value                                            (TokenName (TokenName))


invoice :: String -> String -> Value Observation -> Slot -> Contract -> Contract
invoice from to amount timeout continue =
    let party        = Role $ TokenName $ fromString from
        counterparty = Role $ TokenName $ fromString to
    in  When
            [ Case
                  (Deposit (AccountId 0 party) party ada amount)
                  (Pay (AccountId 0 party)
                       (Party counterparty)
                       ada
                       amount
                       continue
                  )
            ]
            timeout
            Close

maxPseudoDecimalValue :: Integer
maxPseudoDecimalValue = 100000000000000

inquiryFs
    :: EventType
    -> String
    -> Slot
    -> String
    -> Contract
    -> Contract
inquiryFs ev timePosfix date oracle continue =
    let
        oracleRole = Role $ TokenName $ fromString oracle
        inputTemplate inputChoiceId inputOwner inputBound cont =
            When
                [ Case
                      (Choice (ChoiceId inputChoiceId inputOwner) inputBound)
                      (Let
                          (ValueId inputChoiceId)
                          (ChoiceValue (ChoiceId inputChoiceId inputOwner))
                          cont
                      )
                ]
                date
                Close

        riskFactorInquiry name = inputTemplate
            (fromString (name ++ timePosfix))
            oracleRole
            [Bound 0 maxPseudoDecimalValue]
        riskFactorsInquiryEv AD = id
        riskFactorsInquiryEv SC = riskFactorInquiry "o_rf_SCMO"
        riskFactorsInquiryEv RR = riskFactorInquiry "o_rf_RRMO"
        riskFactorsInquiryEv PP =
            riskFactorInquiry "o_rf_CURS" .
                riskFactorInquiry "pp_payoff"
        riskFactorsInquiryEv _ = riskFactorInquiry "o_rf_CURS"
    in
        riskFactorsInquiryEv ev continue

genProjectedCashflows :: ContractTerms -> [CashFlow]
genProjectedCashflows terms =
    let
        eventTypes   = [IED, MD, RR, IP]
        analysisDate = fromGregorian 2008 10 22
        riskFactors = RiskFactors 1.0 1.0 1.0 1.0 analysisDate

        preserveDate e d = (e, d)
        getSchedule e = fromMaybe [] $ schedule e terms
        scheduleEvent e = preserveDate e <$> getSchedule e
        events = concatMap scheduleEvent eventTypes

        applyStateTransition (st, ev, date) (ev', date') =
            (stateTransition ev riskFactors terms st (calculationDay date), ev', date')
        calculatePayoff (st, ev, date) =
            payoff ev riskFactors terms st (calculationDay date)

        initialState =
            ( inititializeState terms
            , AD
            , ShiftedDay analysisDate analysisDate
            )
        states  = L.tail $ L.scanl applyStateTransition initialState events
        payoffs = calculatePayoff <$> states

        genCashflow ((_, ev, d), pff) = CashFlow
            { tick               = 0
            , cashContractId     = "0"
            , cashParty          = "party"
            , cashCounterParty   = "counterparty"
            , cashPaymentDay     = paymentDay d
            , cashCalculationDay = calculationDay d
            , cashEvent          = ev
            , amount             = pff
            , currency           = "ada"
            }
    in
        genCashflow <$> L.zip states payoffs

genStaticContract :: ContractTerms -> Contract
genStaticContract terms =
    let
        cfs = genProjectedCashflows terms
        gen CashFlow{..} = invoice "party" "counterparty" (Constant $ round amount) (Slot $ dayToSlotNumber cashPaymentDay)
    in foldl (flip gen) Close cfs


genFsContract :: ContractTerms -> Contract
genFsContract terms =
    let
        payoffAt t = ValueId $ fromString $ "payoff_" ++ show t
        schedCfs = genProjectedCashflows terms
        schedEvents = cashEvent <$> schedCfs
        schedDates = Slot . dayToSlotNumber . cashPaymentDay <$> schedCfs
        cfsDirections = amount <$> schedCfs
        gen :: (CashFlow, EventType, Slot, Double, Integer) -> Contract -> Contract
        gen (cf, ev, date, r, t) cont = inquiryFs ev ("_" ++ show t) date "oracle"
            $ stateTransitionFs ev terms t (cashCalculationDay cf)
            $ Let (payoffAt t) (payoffFs ev terms t (cashCalculationDay cf))
            $ if r > 0.0    then invoice "party" "counterparty" (UseValue $ payoffAt t) date cont
                            else invoice "counterparty" "party" (NegValue $ UseValue $ payoffAt t) date cont
        scheduleAcc = foldr gen Close $ L.zip5 schedCfs schedEvents schedDates cfsDirections [1..]
    in inititializeStateFs terms scheduleAcc
