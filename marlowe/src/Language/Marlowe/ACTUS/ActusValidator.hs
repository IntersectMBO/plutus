{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.ActusValidator where

import Language.Marlowe.ACTUS.ContractTerms
import Language.Marlowe.ACTUS.Schedule
import Language.Marlowe.ACTUS.BusinessEvents
import Language.Marlowe.ACTUS.SCHED.ContractSchedule
import Language.Marlowe.ACTUS.INIT.StateInitialization
import Language.Marlowe.ACTUS.POF.Payoff
import Language.Marlowe.ACTUS.STF.StateTransition

import Data.Time
import Data.Maybe
import Control.Arrow

import qualified Data.List as L

genShiftedSchedule :: EventType -> ContractTerms -> Maybe ShiftedSchedule
genShiftedSchedule = schedule

isPaymentDay :: Day -> ShiftedSchedule -> Bool
isPaymentDay day = fmap paymentDay >>> L.elem day

type ValidatedCashFlows = [CashFlow]

checkAllScheduledEventsHappened :: Day -> ShiftedSchedule -> ValidatedCashFlows -> Bool
checkAllScheduledEventsHappened present schedule past = True --todo: minus credit events in past

replayValidatedEvents :: ContractTerms -> [CashFlow] -> CashFlow -> Double
replayValidatedEvents terms past present =
    let applyStateTransition st cf = stateTransition (cashEvent cf) terms st (cashCalculationDay cf)
        calculatePayoff st cf = payoff (cashEvent cf) terms st (cashCalculationDay cf)
        initialState = inititializeState terms
        memory = L.foldl applyStateTransition initialState past
    in calculatePayoff memory present

-- validated cashflows are part of transaction state, present is proposed cashflow
validateCashFlow :: ContractTerms -> ValidatedCashFlows -> CashFlow -> Bool
validateCashFlow terms past present = 
    let schedule = fromMaybe [] (genShiftedSchedule (mapEventType (cashEvent present)) terms)
        noUnreportedOverdue = checkAllScheduledEventsHappened (cashPaymentDay present) schedule past 
    in case (cashEvent present) of 
        AD_EVENT {..} -> True
        PP_EVENT {..} -> noUnreportedOverdue -- maybe check that outstanding notional is still positive and compare pp_payoff to amount
        CE_EVENT {..} -> not noUnreportedOverdue  
        _ -> 
            let 
                expectedPaymentDayOk = isPaymentDay (cashPaymentDay present) schedule
                expectedPayOff = replayValidatedEvents terms past present
            in noUnreportedOverdue && expectedPaymentDayOk && expectedPayOff == amount present
    --todo check currency from contract terms
    --todocheck contractId
    --todo check if party is eligble to initate this event

