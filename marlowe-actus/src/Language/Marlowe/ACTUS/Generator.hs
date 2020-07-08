{-# LANGUAGE RecordWildCards #-}

{- This module contains templates for Marlowe constructs required by ACTUS logic -}
module Language.Marlowe.ACTUS.Generator
    ( 
    genStaticContract
    , genFsContract
    , genProjectedCashflows
    )
where

import Data.Time ( fromGregorian )
import Ledger.Value ( TokenName(TokenName) )
import Data.String ( IsString(fromString) )
import qualified Language.PlutusTx.AssocMap as Map
    ( insert, keys, empty, lookup )
import Data.Maybe ( fromJust, fromMaybe, isJust )
import qualified Data.List as L ( init, last, zip, scanl, tail, zip5 )
import Language.Marlowe
    ( 
      ada,
      AccountId(AccountId),
      Action(Choice, Deposit),
      Bound(Bound),
      Case(Case),
      ChoiceId(ChoiceId),
      Contract(Close, Pay, When, Let),
      Observation,
      Party(Role),
      Payee(Party),
      State(..),
      TransactionOutput(..),
      Value(UseValue, ChoiceValue, Constant, NegValue),
      ValueId(ValueId),
      Slot(..) )
import Language.Marlowe.ACTUS.Definitions.Schedule ( CashFlow(..), calculationDay, paymentDay, ShiftedDay(..) )
import Language.Marlowe.ACTUS.Definitions.ContractTerms ( ContractTerms )
import Language.Marlowe.ACTUS.Definitions.BusinessEvents
    ( ScheduledEvent(..),
      EventType(..),
      eventTypeIdToEventType,
      projectEvent,
      mapEventType )
import Language.Marlowe.ACTUS.MarloweCompat
import Language.Marlowe.ACTUS.Model.POF.PayoffFs
import Language.Marlowe.ACTUS.Model.POF.Payoff
import Language.Marlowe.ACTUS.Model.STF.StateTransition
import Language.Marlowe.ACTUS.Model.STF.StateTransitionFs
import Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule
import Language.Marlowe.ACTUS.Model.INIT.StateInitializationFs
import Language.Marlowe.ACTUS.Model.INIT.StateInitialization


type TimePostfix = String -- sequence number of event
type Amount = (Language.Marlowe.Value Language.Marlowe.Observation)
type Oracle = String
type EventInitiatorParty = String
type From = String
type To = String
type Continuation = Contract
type EventInitiatorPartyId = Integer


invoice :: From -> To -> Amount -> Slot -> Continuation -> Contract
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

inquiryFs
    :: EventType
    -> TimePostfix
    -> Slot
    -> Oracle
    -> Continuation
    -> Contract
inquiryFs ev timePosfix date oracle continue =
    let
        oracleRole = Role $ TokenName $ fromString oracle
        inputTemplate inputChoiceId inputOwner inputBound cont =
            (When
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
            )
        riskFactorInquiry name = inputTemplate
            (fromString (name ++ timePosfix))
            oracleRole
            [Bound 0 100000000000000]
        riskFactorsInquiryEv AD = id
        riskFactorsInquiryEv SC = riskFactorInquiry "o_rf_SCMO"
        riskFactorsInquiryEv RR = riskFactorInquiry "o_rf_RRMO"    
        riskFactorsInquiryEv PP = 
            riskFactorInquiry "o_rf_CURS" .
                riskFactorInquiry "pp_payoff"  
        riskFactorsInquiryEv _ = riskFactorInquiry "o_rf_CURS"
    in
        (riskFactorsInquiryEv ev) continue

genProjectedCashflows :: ContractTerms -> [CashFlow]
genProjectedCashflows terms =
    let
        eventTypes   = [IED, MD]
        analysisDate = fromGregorian 2008 10 22

        projectPreserveDate e d = (projectEvent e, d)
        getSchedule e = fromMaybe [] $ schedule e terms
        scheduleEvent e = projectPreserveDate e <$> getSchedule e
        events = concatMap scheduleEvent eventTypes

        applyStateTransition (st, ev, date) (ev', date') =
            (stateTransition ev terms st (calculationDay date), ev', date')
        calculatePayoff (st, ev, date) =
            payoff ev terms st (calculationDay date)

        initialState =
            ( inititializeState terms
            , projectEvent AD
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
        schedEvents = mapEventType . cashEvent <$> schedCfs
        schedDates = Slot . dayToSlotNumber . cashPaymentDay <$> schedCfs
        cfsDirections = amount <$> schedCfs
        gen (cf, ev, date, r, t) cont = inquiryFs ev ("_" ++ show t) date "oracle"
            $ stateTransitionFs ev terms t (cashCalculationDay cf)
            $ Let (payoffAt t) (payoffFs ev terms t)
            $ if r > 0.0    then invoice "party" "counterparty" (UseValue $ payoffAt t) date cont
                            else invoice "counterparty" "party" (NegValue $ UseValue $ payoffAt t) date cont
        schedule = foldl (flip gen) Close $ reverse $ L.zip5 schedCfs schedEvents schedDates cfsDirections [1..]
    in inititializeStateFs terms schedule
