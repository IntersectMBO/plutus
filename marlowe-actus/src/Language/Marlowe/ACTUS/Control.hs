{-# LANGUAGE RecordWildCards #-}

{- This module contains templates for Marlowe constructs required by ACTUS logic -}
module Language.Marlowe.ACTUS.Control
    ( invoice
    , inquiry
    , genContract
    , stateParser
    , actusMarloweValidator
    , appendPresentState
    )
where

import Data.Time ( fromGregorian )
import Ledger.Value ( TokenName(TokenName) )
import Data.String ( IsString(fromString) )
import qualified Language.PlutusTx.AssocMap as Map
    ( insert, keys, empty, lookup )
import Data.Maybe ( fromJust, fromMaybe, isJust )
import qualified Data.List as L ( init, last )
import Language.Marlowe
    ( marloweFixedPoint,
      ada,
      AccountId(AccountId),
      Action(Choice, Deposit),
      Bound(Bound),
      Case(Case),
      ChoiceId(ChoiceId),
      Contract(Close, Pay, When, Let),
      LogicalTime,
      LoopState(LoopState, originalContract, logicalTime, stateHistory),
      Observation,
      Party(Role),
      Payee(Party),
      State(..),
      TransactionOutput(..),
      Value(UseValue, ChoiceValue, Constant),
      ValueId(ValueId),
      Slot )
import Language.Marlowe.ACTUS.Schedule ( CashFlow(..) )
import Language.Marlowe.ACTUS.ContractTerms ( ContractTerms )
import Language.Marlowe.ACTUS.BusinessEvents
    ( ScheduledEvent(..),
      EventType(..),
      eventTypeIdToEventType )
import Language.Marlowe.ACTUS.ActusValidator ( validateCashFlow )

type TimePostfix = String -- sequence number of event
type Amount = (Language.Marlowe.Value Language.Marlowe.Observation)
type Oracle = String
type EventInitiatorParty = String
type From = String
type To = String
type Continuation = Contract
type EventInitiatorPartyId = Integer

--todo check roleSign, enforce a date
invoice :: From -> To -> Amount -> Slot -> Continuation -> Contract
invoice from to amount timeout continue =
    let party        = Role $ TokenName $ fromString from
        counterparty = Role $ TokenName $ fromString to
    in  When
            [ Case
                  (Deposit (AccountId 0 party) party ada amount)
                  (Pay (AccountId 1 counterparty)
                       (Party party)
                       ada
                       amount
                       continue
                  )
            ]
            timeout
            Close

--roleSign :: TimePostfix -> String -> MarloweBool
--roleSign postfix choiceName = TrueObs --todo use ChoiceValue in order to check which party made a choice

--todo read payment date 
inquiry
    :: TimePostfix
    -> EventInitiatorParty
    -> EventInitiatorPartyId
    -> Oracle
    -> Continuation
    -> Contract
inquiry timePosfix party partyId oracle continue =
    let
        partyRole  = Role $ TokenName $ fromString party
        oracleRole = Role $ TokenName $ fromString oracle
        inputTemplate inputChoiceId inputOwner inputDefault inputBound cont =
            (When
                [ Case
                      (Choice (ChoiceId inputChoiceId inputOwner) inputBound)
                      (Let
                          (ValueId inputChoiceId)
                          (ChoiceValue (ChoiceId inputChoiceId inputOwner)
                                       inputDefault
                          )
                          cont
                      )
                ]
                1000000000
                Close
            )
        contractIdInquiry = inputTemplate
            (fromString ("contractId" ++ timePosfix))
            partyRole
            (Constant 0)
            [Bound 0 1000000]
        eventTypeInquiry = inputTemplate
            (fromString ("eventType" ++ timePosfix))
            partyRole
            (Constant 0)
            [Bound 0 1000000]
        riskFactorInquiry name = inputTemplate
            (fromString ("riskFactor-" ++ name ++ timePosfix))
            oracleRole
            (Constant 0)
            [Bound 0 1000000]
        payoffInquiry = inputTemplate (fromString ("payoff" ++ timePosfix))
                                      partyRole
                                      (Constant 0)
                                      [Bound 0 1000000]
        payoffCurrencyInquiry = inputTemplate
            (fromString ("payoffCurrency" ++ timePosfix))
            partyRole
            (Constant 0)
            [Bound 0 1000000]
        addEventInitiatorParty =
            Let (ValueId (fromString "party")) (Constant partyId)
        riskFactorsInquiry =
            riskFactorInquiry "o_rf_CURS"
                . riskFactorInquiry "o_rf_RRMO"
                . riskFactorInquiry "o_rf_SCMO"
                . riskFactorInquiry "pp_payoff"
    in
        ( contractIdInquiry
            . eventTypeInquiry
            . riskFactorsInquiry
            . payoffInquiry
            . payoffCurrencyInquiry
            . addEventInitiatorParty
            )
            continue

genContract :: Contract
genContract = inquiry "" "party" 0 "oracle" $ invoice
    "party"
    "counterparty"
    (UseValue $ ValueId (fromString "payoff"))
    1000000000
    Close

--The logic below happens inside a smart-contract--

parseDouble :: Integer -> Double
parseDouble int = fromIntegral int / marloweFixedPoint


appendPresentState :: State -> State
appendPresentState state =
    if isJust $ Map.lookup (ValueId $ fromString "payoffCurrency")
                           (boundValues state)
        then
            let emptyLoopSt = LoopState { originalContract = undefined
                                        , logicalTime      = 0
                                        , stateHistory     = Map.empty
                                        }
                loopSt = fromMaybe emptyLoopSt (loopState state)
                state' = state
                    { loopState = Just
                        (loopSt
                            { originalContract = Close
                            , logicalTime      = logicalTime loopSt + 1
                            , stateHistory     = Map.insert
                                                     (logicalTime loopSt)
                                                     (boundValues state)
                                                     (stateHistory loopSt)
                            }
                        )
                    }
            in  state'
        else state

stateParser :: State -> [CashFlow]
stateParser State {..} =
    let
        stateHist = stateHistory $ fromJust loopState
        parseCashFlow :: LogicalTime -> CashFlow
        parseCashFlow t =
            let
                look :: String -> Integer
                look name =
                    fromJust
                        $ Map.lookup (ValueId $ fromString name)
                        $ fromJust
                        $ Map.lookup t stateHist
                proposedPaymentDate = fromGregorian 2008 10 20 --todo slotRangeToDay (look "paymentSlotStart") (look "paymentSlotEnd") 
                parseCashEvent eventId = case eventTypeIdToEventType eventId of
                    AD -> AD_EVENT $ parseDouble $ look "riskFactor-o_rf_CURS"
                    IED ->
                        IED_EVENT $ parseDouble $ look "riskFactor-o_rf_CURS"
                    PR -> PR_EVENT $ parseDouble $ look "riskFactor-o_rf_CURS"
                    PI -> PI_EVENT $ parseDouble $ look "riskFactor-o_rf_CURS"

                    PRF ->
                        PRF_EVENT $ parseDouble $ look "riskFactor-o_rf_CURS"

                    PY -> PY_EVENT
                        { o_rf_CURS = parseDouble $ look "riskFactor-ro_rf_CURS"
                        , o_rf_RRMO = parseDouble $ look "riskFactor-o_rf_RRMO"
                        }
                    FP -> FP_EVENT $ parseDouble $ look "riskFactor-o_rf_CURS"
                    PRD ->
                        PRD_EVENT $ parseDouble $ look "riskFactor-o_rf_CURS"
                    TD -> TD_EVENT $ parseDouble $ look "riskFactor-o_rf_CURS"
                    IP -> IP_EVENT $ parseDouble $ look "riskFactor-o_rf_CURS"
                    IPCI ->
                        IPCI_EVENT $ parseDouble $ look "riskFactor-o_rf_CURS"
                    IPCB ->
                        IPCB_EVENT $ parseDouble $ look "riskFactor-o_rf_CURS"
                    RR -> RR_EVENT
                        { o_rf_CURS = parseDouble $ look "riskFactor-o_rf_CURS"
                        , o_rf_RRMO = parseDouble $ look "riskFactor-o_rf_RRMO"
                        }
                    RRF ->
                        RRF_EVENT $ parseDouble $ look "riskFactor-o_rf_CURS"
                    SC -> SC_EVENT
                        { o_rf_CURS = parseDouble $ look "riskFactor-o_rf_CURS"
                        , o_rf_SCMO = parseDouble $ look "riskFactor-o_rf_SCMO"
                        }
                    XD -> XD_EVENT $ parseDouble $ look "riskFactor-o_rf_CURS"
                    DV -> DV_EVENT $ parseDouble $ look "riskFactor-o_rf_CURS"
                    --todo: imports
                    Language.Marlowe.ACTUS.BusinessEvents.MR ->
                        MR_EVENT $ parseDouble $ look "riskFactor-o_rf_CURS"
                    STD ->
                        STD_EVENT $ parseDouble $ look "riskFactor-o_rf_CURS"
                    MD -> MD_EVENT $ parseDouble $ look "riskFactor-o_rf_CURS"
                    PP -> PP_EVENT
                        { pp_payoff = parseDouble $ look "riskFactor-pp_payoff"
                        , o_rf_CURS = parseDouble $ look "riskFactor-o_rf_CURS"
                        }
                    CE -> CE_EVENT
                        { creditDate = proposedPaymentDate
                        , o_rf_CURS  = parseDouble $ look "riskFactor-o_rf_CURS"
                        }
            in
                CashFlow { tick               = t
                         , cashContractId     = show $ look "contractId"
                         , cashParty          = show $ look "party"
                         , cashCounterParty   = show $ look "counterparty"
                         , cashPaymentDay     = proposedPaymentDate
                         , cashCalculationDay = undefined
                         , cashEvent = parseCashEvent $ look "eventType"
                         , amount             = parseDouble $ look "amount"
                         , currency           = show $ look "currency"
                         }
    in
        if isJust loopState then parseCashFlow <$> Map.keys stateHist else []

actusMarloweValidator :: ContractTerms -> TransactionOutput -> Bool
actusMarloweValidator terms TransactionOutput {..} =
    let cashflows = stateParser $ appendPresentState txOutState
        result    = validateCashFlow terms (L.init cashflows) (L.last cashflows) --todo THIS IS NOT SECURE
    in  null cashflows || result
actusMarloweValidator _ (Error _) = False

