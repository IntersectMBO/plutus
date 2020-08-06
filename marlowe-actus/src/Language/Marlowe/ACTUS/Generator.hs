{-# LANGUAGE RecordWildCards #-}

{- This module contains templates for Marlowe constructs required by ACTUS logic -}
module Language.Marlowe.ACTUS.Generator
    (
    genStaticContract
    , genFsContract
    , genProjectedCashflows
    )
where

import qualified Data.List                                               as L (scanl, tail, zip, zip6)
import           Data.Maybe                                              (fromMaybe, isNothing)
import           Data.String                                             (IsString (fromString))
import           Data.Sort                                               (sortOn)                               
import           Data.Time                                               (Day, fromGregorian)
import           Language.Marlowe                                        (AccountId (AccountId),
                                                                          Action (Choice, Deposit), Bound (Bound),
                                                                          Case (Case), ChoiceId (ChoiceId),
                                                                          Contract (Close, Let, Pay, When), Observation,
                                                                          Party (Role), Payee (Party), Slot (..),
                                                                          Value (ChoiceValue, Constant, NegValue, UseValue),
                                                                          ValueId (ValueId), ada)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents       (EventType (..), RiskFactors (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms        (ContractTerms(ct_CURS, ct_SD, constraints), Assertions(..), AssertionContext(..))
import           Language.Marlowe.ACTUS.Definitions.Schedule             (CashFlow (..), ShiftedDay (..),
                                                                          calculationDay, paymentDay)
import           Language.Marlowe.ACTUS.MarloweCompat                    (dayToSlotNumber, constnt, toMarloweFixedPoint)
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
    -> ContractTerms
    -> String
    -> Slot
    -> String
    -> Maybe AssertionContext
    -> Contract
    -> Contract
inquiryFs ev ct timePosfix date oracle context continue =
    let
        oracleRole = Role $ TokenName $ fromString oracle
        letTemplate inputChoiceId inputOwner cont = 
            Let
                (ValueId inputChoiceId)
                (ChoiceValue (ChoiceId inputChoiceId inputOwner))
                cont
                      
        inputTemplate inputChoiceId inputOwner inputBound cont =
            When
                [ Case (Choice (ChoiceId inputChoiceId inputOwner) inputBound) $
                    letTemplate inputChoiceId inputOwner cont
                ]
                date
                Close

        inferBounds name ctx = case (name, ctx) of
            ("o_rf_RRMO", Just AssertionContext{..}) -> 
                [Bound (toMarloweFixedPoint rrmoMin) (toMarloweFixedPoint rrmoMax)]
            _ -> [Bound 0 maxPseudoDecimalValue]
        riskFactorInquiry name = inputTemplate
            (fromString (name ++ timePosfix))
            oracleRole
            (inferBounds name context)
        riskFactorsInquiryEv AD = id
        riskFactorsInquiryEv SC = riskFactorInquiry "o_rf_SCMO"
        riskFactorsInquiryEv RR = riskFactorInquiry "o_rf_RRMO"
        riskFactorsInquiryEv PP =
            riskFactorInquiry "o_rf_CURS" .
                riskFactorInquiry "pp_payoff"
        riskFactorsInquiryEv _ = 
            if ct_CURS ct then riskFactorInquiry "o_rf_CURS" 
            else Let (ValueId (fromString ("o_rf_CURS" ++ timePosfix))) (constnt 1.0)
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
        sortOn cashPaymentDay $ genCashflow <$> L.zip states payoffs

genStaticContract :: ContractTerms -> Contract
genStaticContract terms =
    let
        cfs = genProjectedCashflows terms
        gen CashFlow{..} = 
            if amount > 0.0 
                then invoice "party" "counterparty" (Constant $ round amount) (Slot $ dayToSlotNumber cashPaymentDay)
                else invoice "counterparty" "party" (Constant $ round $ -amount) (Slot $ dayToSlotNumber cashPaymentDay)
    in foldl (flip gen) Close cfs


genFsContract :: ContractTerms -> Contract
genFsContract terms =
    let
        payoffAt t = ValueId $ fromString $ "payoff_" ++ show t
        schedCfs = genProjectedCashflows terms
        schedEvents = cashEvent <$> schedCfs
        schedDates = Slot . dayToSlotNumber . cashPaymentDay <$> schedCfs
        previousDates = ([ct_SD terms] ++ (cashCalculationDay <$> schedCfs))
        cfsDirections = amount <$> schedCfs
        ctx = context <$> constraints terms
        gen :: (CashFlow, Day, EventType, Slot, Double, Integer) -> Contract -> Contract
        gen (cf, prevDate, ev, date, r, t) cont = 
            inquiryFs ev terms ("_" ++ show t) date "oracle" ctx
            $ stateTransitionFs ev terms t prevDate (cashCalculationDay cf)
            $ Let (payoffAt t) (fromMaybe (constnt 0.0) pof)
            $ if (isNothing pof) then cont
              else if  r > 0.0   then invoice "party" "counterparty" (UseValue $ payoffAt t) date cont
              else                    invoice "counterparty" "party" (NegValue $ UseValue $ payoffAt t) date cont
            where pof = (payoffFs ev terms t (t - 1) prevDate (cashCalculationDay cf))
        scheduleAcc = foldr gen Close $ L.zip6 schedCfs previousDates schedEvents schedDates cfsDirections [1..]
    in inititializeStateFs terms scheduleAcc
