{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.ActusValidator where

import Language.Marlowe.ACTUS.ContractTerms ( ContractTerms )
import Language.Marlowe.ACTUS.Schedule
    ( CashFlow(cashCalculationDay, cashEvent, cashPaymentDay, amount),
      ShiftedSchedule,
      ShiftedDay(paymentDay) )
import Language.Marlowe.ACTUS.BusinessEvents
    ( ScheduledEvent(CE_EVENT, AD_EVENT, PP_EVENT, pp_payoff,
                     o_rf_CURS, creditDate),
      EventType,
      mapEventType )
import Language.Marlowe.ACTUS.SCHED.ContractSchedule ( schedule )
import Language.Marlowe.ACTUS.INIT.StateInitialization
    ( inititializeState )
import Language.Marlowe.ACTUS.POF.Payoff ( payoff )
import Language.Marlowe.ACTUS.STF.StateTransition
    ( stateTransition )
import Data.Time ( Day )
import Data.Maybe ( fromMaybe )
import Control.Arrow ( (>>>) )
import qualified Data.List as L ( foldl, elem )


genShiftedSchedule :: EventType -> ContractTerms -> Maybe ShiftedSchedule
genShiftedSchedule = schedule

isPaymentDay :: Day -> ShiftedSchedule -> Bool
isPaymentDay day = fmap paymentDay >>> L.elem day

type ValidatedCashFlows = [CashFlow]

checkAllScheduledEventsHappened
    :: Day -> ShiftedSchedule -> ValidatedCashFlows -> Bool
checkAllScheduledEventsHappened _ _ _ = True --todo: minus credit events in past

replayValidatedEvents :: ContractTerms -> [CashFlow] -> CashFlow -> Double
replayValidatedEvents terms past present =
    let applyStateTransition st cf =
                stateTransition (cashEvent cf) terms st (cashCalculationDay cf)
        calculatePayoff st cf =
                payoff (cashEvent cf) terms st (cashCalculationDay cf)
        initialState = inititializeState terms
        memory       = L.foldl applyStateTransition initialState past
    in  calculatePayoff memory present

-- validated cashflows are part of transaction state, present is proposed cashflow
validateCashFlow :: ContractTerms -> ValidatedCashFlows -> CashFlow -> Bool
validateCashFlow terms past present =
    let
        sched = fromMaybe
            []
            (genShiftedSchedule (mapEventType (cashEvent present)) terms)
            
        noUnreportedOverdue = checkAllScheduledEventsHappened
            (cashPaymentDay present)
            sched
            past
    in
        case cashEvent present of
            AD_EVENT {..} -> True
            PP_EVENT {..} -> (noUnreportedOverdue || error "unreported overdue") -- maybe check that outstanding notional is still positive and compare pp_payoff to amount
            CE_EVENT {..} -> not noUnreportedOverdue
            _ ->
                let expectedPaymentDayOk =
                            isPaymentDay (cashPaymentDay present) sched
                    expectedPayOff = replayValidatedEvents terms past present
                in  (noUnreportedOverdue || error "unreported overdue") 
                        && (expectedPaymentDayOk || (error $ "payment day is not ok: " ++ (show $ cashPaymentDay present)))
                        && (abs expectedPayOff == amount present || (error $ "payoff is not ok, expected: " ++ show expectedPayOff ++ " actual: " ++ (show $ amount present) ))
    --todo get rid of abs
    --todo check currency from contract terms
    --todocheck contractId
    --todo check if party is eligble to initate this event

