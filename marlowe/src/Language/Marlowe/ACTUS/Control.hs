{-# LANGUAGE RecordWildCards #-}

{- This module contains templates for Marlowe constructs required by ACTUS logic -}
module Language.Marlowe.ACTUS.Control where

import Language.Marlowe
import Data.Time
import Data.Time.Clock
import Data.Time.Clock.POSIX
import Data.Time.Clock.System
import Wallet 
import Ledger.Crypto
import Ledger.Value
import Data.String (IsString (fromString))
import Language.PlutusTx.AssocMap (Map)
import qualified Language.PlutusTx.AssocMap as Map
import Data.Maybe
import Data.Map.Strict
import qualified Data.Maybe as Maybe
import Data.List
import qualified Data.List as L
import Data.Map
import qualified Data.Map as Mp
import Language.Marlowe.ACTUS.Schedule
import Language.Marlowe.ACTUS.ContractTerms
import Language.Marlowe.ACTUS.BusinessEvents
import Language.Marlowe.ACTUS.ActusValidator
import Control.Arrow
import Text.Regex.Posix

type Currency = String
type Tkn = String
type TimePostfix = String -- sequence number of event
type Amount = Language.Marlowe.Value
type MarloweBool = Language.Marlowe.Observation
type Oracle = String
type EventInitiatorParty = String
type From = String
type To = String
type Continuation = Contract
type EventInitiatorPartyId = Integer

cardanoEpochStart = 100
marloweFixedPoint = 1000000000

dayToSlotNumber :: Day -> Integer
dayToSlotNumber d = let
    (MkSystemTime secs _) = utcToSystemTime (UTCTime d 0)
    in fromIntegral secs - cardanoEpochStart `mod` 20

slotRangeToDay :: Integer -> Integer -> Day
slotRangeToDay start end = undefined

--todo check roleSign, enforce a date
invoice :: From -> To -> Day -> Amount -> Currency -> Tkn -> Continuation -> Contract
invoice from to date amount currency tokenName continue = 
    let
        party = Role $ TokenName $ fromString from
        counterparty = Role $ TokenName $ fromString to
    in 
    When
        [Case
            (Deposit (AccountId 0 party) party ada amount)
                (Pay (AccountId 1 counterparty) (Party party) ada amount 
                    continue)]
    100 Close 

roleSign :: TimePostfix -> String -> MarloweBool
roleSign postfix choiceName = TrueObs --todo use ChoiceValue in order to check which party made a choice

--todo read payment date 
inquiry :: TimePostfix -> EventInitiatorParty -> EventInitiatorPartyId -> Oracle -> Contract -> Contract
inquiry timePosfix party partyId oracle continue = let
    partyRole = Role $ TokenName $ fromString party
    oracleRole = Role $ TokenName $ fromString oracle
    inputTemplate inputChoiceId inputOwner inputDefault inputBound cont = 
        (When
            [Case (Choice (ChoiceId inputChoiceId inputOwner) inputBound)
                (Let (ValueId inputChoiceId) (ChoiceValue (ChoiceId inputChoiceId inputOwner) inputDefault)
                    cont)]
            0
            Close) 
    contractIdInquiry cont = inputTemplate 
        (fromString ("contractId" ++ timePosfix)) 
        partyRole 
        (Constant 0) 
        [Bound 0 1000000] 
        cont
    eventTypeInquiry cont = inputTemplate 
        (fromString ("eventType" ++ timePosfix))
        partyRole 
        (Constant 0) 
        [Bound 0 1000000] 
        cont   
    riskFactorInquiry name cont = inputTemplate 
        (fromString ("riskFactor-" ++ i ++ timePosfix)) 
        oracleRole 
        (Constant 0) 
        [Bound 0 1000000] 
        cont
    payoffInquiry cont = inputTemplate 
        (fromString ("payoff" ++ timePosfix)) 
        partyRole 
        (Constant 0) 
        [Bound 0 1000000] 
        cont
    payoffCurrencyInquiry cont = inputTemplate 
        (fromString ("payoffCurrency" ++ timePosfix)) 
        partyRole 
        (Constant 0) 
        [Bound 0 1000000] 
        cont
    paymentSlotStartInquiry cont = inputTemplate 
        (fromString ("paymentSlotStart" ++ timePosfix)) 
        partyRole 
        (Constant 0) 
        [Bound 0 1000000] 
        cont
    paymentSlotStartInquiry cont = inputTemplate 
        (fromString ("paymentSlotEnd" ++ timePosfix)) 
        partyRole 
        (Constant 0) 
        [Bound 0 1000000] 
        cont
    addEventInitiatorParty cont = (Let (ValueId (fromString "party")) (Constant partyId) cont)
    riskFactorsInquiry = 
        (riskFactorInquiry "o_rf_CURS") >>> 
        (riskFactorInquiry "o_rf_RRMO") >>> 
        (riskFactorInquiry "o_rf_SCMO") >>>
        (riskFactorInquiry "pp_payoff")
    in (contractIdInquiry >>> 
        eventTypeInquiry >>> 
        riskFactorsInquiry >>> 
        payoffInquiry >>> 
        payoffCurrencyInquiry >>> 
        addEventInitiatorParty
    ) continue

--todo: combine invoice and inquiry
genContract :: [EventInitiatorParty] -> [EventInitiatorPartyId] -> Oracle -> Contract
genContract parties partyIds oracle = Close

data ContractVariable = ContractVariable {
    tickN :: Integer,
    variableName :: String,
    variableValue :: Integer
}

parseDouble :: Integer -> Double
parseDouble int = (fromIntegral int) / marloweFixedPoint

stateParser :: State -> [CashFlow] --todo should we raise error if last cashflow's event is only partially parsable?
stateParser state =
    let 
        parseVariable :: (String, Integer) -> ContractVariable
        parseVariable (name, value) = ContractVariable {
            tickN = read $ name =~ ".*_t(.*)",
            variableName = name =~ "(.*)_t.*",
            variableValue = value
        }
        isCompleteCashflow vars = 
            -- todo: is there enough fields for cash flow 
            -- todo: we should also validate that only last t has isCompleteCashflow = False
            -- it is allowed for partial interpreter state
            True 
        parseCashFlowFromVars :: [ContractVariable] -> CashFlow    
        parseCashFlowFromVars vars = 
            let
                t = tickN (head vars)
                varsMap = Mp.fromList $ fmap (variableName &&& variableValue) vars
                look :: String -> Integer
                look name = fromJust $ Mp.lookup name varsMap
                proposedPaymentDate = slotRangeToDay (look "paymentSlotStart") (look "paymentSlotEnd") 
                parseCashEvent id = case eventTypeIdToEventType id of
                    AD   -> AD_EVENT {o_rf_CURS = parseDouble $ look "riskFactor-o_rf_CURS"}
                    IED  -> IED_EVENT {o_rf_CURS  = parseDouble $ look "riskFactor-o_rf_CURS"}   
                    PR   -> PR_EVENT {o_rf_CURS  = parseDouble $ look "riskFactor-o_rf_CURS"}  
                    PI   -> PI_EVENT {o_rf_CURS  = parseDouble $ look "riskFactor-o_rf_CURS"}  
                    PRF  -> PRF_EVENT {o_rf_CURS  = parseDouble $ look "riskFactor-o_rf_CURS"}  
                    PY   -> PY_EVENT {
                        o_rf_CURS = parseDouble $ look "riskFacto-ro_rf_CURS", 
                        o_rf_RRMO = parseDouble $ look "riskFactor-o_rf_RRMO"
                    }   
                    FP   -> FP_EVENT {o_rf_CURS  = parseDouble $ look "riskFactor-o_rf_CURS"}   
                    PRD  -> PRD_EVENT {o_rf_CURS  = parseDouble $ look "riskFactor-o_rf_CURS"}
                    TD   -> TD_EVENT {o_rf_CURS  = parseDouble $ look "riskFactor-o_rf_CURS"}  
                    IP   -> IP_EVENT {o_rf_CURS  = parseDouble $ look "riskFactor-o_rf_CURS"}   
                    IPCI -> IPCI_EVENT {o_rf_CURS  = parseDouble $ look "riskFactor-o_rf_CURS"} 
                    IPCB -> IPCB_EVENT {o_rf_CURS  = parseDouble $ look "riskFactor-o_rf_CURS"}
                    RR   -> RR_EVENT {
                        o_rf_CURS = parseDouble $ look "riskFactor-o_rf_CURS", 
                        o_rf_RRMO = parseDouble $ look "riskFactor-o_rf_RRMO"
                    }   
                    RRF  -> RRF_EVENT {o_rf_CURS  = parseDouble $ look "riskFactor-o_rf_CURS"}
                    SC   -> SC_EVENT {
                        o_rf_CURS = parseDouble $ look "riskFactor-o_rf_CURS", 
                        o_rf_SCMO = parseDouble $ look "riskFactor-o_rf_SCMO"
                    }   
                    XD   -> XD_EVENT {o_rf_CURS  = parseDouble $ look "riskFactor-o_rf_CURS"}
                    DV   -> DV_EVENT {o_rf_CURS  = parseDouble $ look "riskFactor-o_rf_CURS"}
                    --todo: imports
                    Language.Marlowe.ACTUS.BusinessEvents.MR -> MR_EVENT {o_rf_CURS  = parseDouble $ look "riskFactor-o_rf_CURS"}
                    STD  -> STD_EVENT {o_rf_CURS  = parseDouble $ look "riskFactor-o_rf_CURS"}
                    MD   -> MD_EVENT {o_rf_CURS  = parseDouble $ look "riskFactor-o_rf_CURS"}
                    PP   -> PP_EVENT { 
                        pp_payoff = parseDouble $ look "riskFactor-pp_payoff", 
                        o_rf_CURS = parseDouble $ look "riskFactor-o_rf_CURS"
                    } 
                    CE   -> CE_EVENT { 
                        date = proposedPaymentDate, 
                        o_rf_CURS = parseDouble $ look "riskFactor-o_rf_CURS"
                    }
            in CashFlow {
                tick = t,
                cashContractId = show $ look "contractId",
                cashParty = show $ look "party",
                cashCounterParty = show $ look "counterparty",
                cashPaymentDay = proposedPaymentDate,
                cashEvent = parseCashEvent $ look "eventType", 
                amount = parseDouble $ look "amount",
                currency = show $ look "currency"
            }
        timeEq val1 val2 = (tickN val1) == (tickN val2)
        flow :: [(String, Integer)] -> [CashFlow]
        flow = (fmap parseVariable) >>> (groupBy timeEq) >>> (L.filter isCompleteCashflow) >>> (fmap parseCashFlowFromVars)
    in [] --flow $ Map.toList $ boundValues state

-- gets cashflows from state parser and passes them to ActusValidator
-- todo: we should validate that contract is of simple form Choice -> Choice -> Pay -> Close
actusMarloweValidator :: ContractTerms -> TransactionOutput -> Bool
actusMarloweValidator terms TransactionOutput{..} = 
    let cashflows = stateParser txOutState
        steps = L.inits cashflows
    in L.foldl (\b -> \l -> b && validateCashFlow terms (L.init l) (L.last l)) True steps --todo simplify, stop early, check empty list
