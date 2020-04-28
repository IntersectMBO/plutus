{-# LANGUAGE RecordWildCards #-}

{- This module contains templates for Marlowe constructs required by ACTUS logic -}
module Language.Marlowe.ACTUS.HP.Control where

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
import qualified Data.Maybe as Maybe
import Data.List
import qualified Data.List as L
import Language.Marlowe.ACTUS.HP.Schedule
import Language.Marlowe.ACTUS.HP.ContractTerms
import Language.Marlowe.ACTUS.HP.ActusValidator

type Currency = String
type Tkn = String
type TimePostfix = String -- sequence number of event
type Amount = Language.Marlowe.Value
type MarloweBool = Language.Marlowe.Observation
type Oracle = String
type InitiatorParty = String
type From = String
type To = String
type Continuation = Contract

cardanoEpochStart = 100

dayToSlotNumber :: Day -> Integer
dayToSlotNumber d = let
    (MkSystemTime secs _) = utcToSystemTime (UTCTime d 0)
    in fromIntegral secs - cardanoEpochStart `mod` 20

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
inquiry :: TimePostfix -> InitiatorParty -> Oracle -> Contract -> Contract
inquiry timePosfix party oracle continue = let
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
    riskFactorInquiry i cont = inputTemplate 
        (fromString ("riskFactor" ++ i ++ timePosfix)) 
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
    riskFactorsInquiry = (riskFactorInquiry "1") . (riskFactorInquiry "2") . (riskFactorInquiry "3")
    in (contractIdInquiry . eventTypeInquiry . riskFactorsInquiry . payoffInquiry . payoffCurrencyInquiry) continue

genContract :: [InitiatorParty] -> Oracle -> Contract
genContract parties oracle = Close

data ContractVariable = ContractVariable {
    t :: Int,
    name :: String,
    value :: Int
}

stateParser :: State -> [CashFlow] --todo should we raise error if last cashflow's event is only partially parsable?
stateParser state =
    let 
        parseVariable nameWithPrefix = ContractVariable {} --todo
        parseCashFlowFromVar var = CashFlow {}
    in [] --todo

-- gets cashflows from state parser and passes them to ActusValidator
actusMarloweValidator :: ContractTerms -> TransactionOutput -> Bool
actusMarloweValidator terms TransactionOutput{..} = 
    let cashflows = stateParser txOutState
        steps = L.inits cashflows
    in L.foldl (\b -> \l -> b && validateCashFlow terms (L.init l) (L.last l)) True steps --todo simplify, stop early, check empty list
