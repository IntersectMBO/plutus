{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.HP.ActusValidator where

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
findPaymentDay day schedule  = Nothing

type ValidatedCashFlows = [CashFlow]

checkAllScheduledEventsHappened :: Day -> ShiftedSchedule -> ValidatedCashFlows -> Bool
checkAllScheduledEventsHappened present schedule past = True --todo: minus credit events in past

--will do STF and POF through all validated events
replayValidatedEvents :: ValidatedCashFlows -> CashFlow -> Double
replayValidatedEvents past present = 0.0

-- validated cashflows are part of transaction state, present is proposed cashflow
validateCashFlow :: ContractTerms -> ValidatedCashFlows -> CashFlow -> Bool
validateCashFlow terms past present@CashFlow{..} = 
    let schedule = (genShiftedSchedule (mapEventType cashEvent) terms)
        noUnreportedOverdue = checkAllScheduledEventsHappened cashPaymentDay schedule past 
    in case cashEvent of 
        PP_EVENT {..} -> noUnreportedOverdue -- maybe check that outstanding notional is still positive and compare pp_payoff to amount
        CE_EVENT {..} -> not noUnreportedOverdue  
        otherwise -> 
            let 
                expectedPaymentDay = findPaymentDay cashPaymentDay schedule
                expectedPayOff = replayValidatedEvents past present
            in noUnreportedOverdue && fromJust expectedPaymentDay == cashPaymentDay && expectedPayOff == amount 
    --todo check currency from contract terms
    --todocheck contractId
    --todo check if party is eligble to initate this event

