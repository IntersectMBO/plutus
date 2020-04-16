{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.HP.ActusValidator where

import Language.Marlowe.ACTUS.HP.Control
import Language.Marlowe.ACTUS.HP.ContractTerms
import Language.Marlowe.ACTUS.HP.Schedule
import Language.Marlowe.ACTUS.HP.BusinessEvents

import Language.Marlowe
import Data.Time
import Data.Map
import Data.Maybe

genShiftedSchedule :: EventType -> ContractTerms -> ShiftedSchedule
genShiftedSchedule eventType terms = []

findPaymentDay :: Day -> ShiftedSchedule -> Maybe Day
findPaymentDay day schedule = Nothing

type ValidatedCashFlows = [CashFlow]

--will do STF and POF through all validated events
replayValidatedEvents :: ValidatedCashFlows -> CashFlow -> Double
replayValidatedEvents past present = 0.0

-- validated cashflows are part of transaction state, present is proposed cashflow
validateCashFlow :: ContractTerms -> ValidatedCashFlows -> CashFlow -> Bool
validateCashFlow terms past present@CashFlow{..} = case cashEvent of 
    PP_EVENT {..} -> True -- maybe check that outstanding notional is still positive and compare pp_payoff to amount
    CE_EVENT {..} -> True 
    otherwise -> 
        let 
            expectedPaymentDay = findPaymentDay cashPaymentDay (genShiftedSchedule (mapEventType cashEvent) terms)
            expectedPayOff = replayValidatedEvents past present
        in fromJust expectedPaymentDay == cashPaymentDay && expectedPayOff == amount 
    --todo check currency from contract terms
    --todocheck contractId
    --todo we need to deduce credit event from validated cash flows

