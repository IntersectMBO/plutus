{- This module contains cashflows that would happen without unscheduled events and risk factors -}

module Language.Marlowe.ACTUS.ProjectedCashFlows where

import Language.Marlowe.ACTUS.ContractTerms ( ContractTerms )
import Language.Marlowe.ACTUS.Schedule
    ( CashFlow(..),
      ShiftedDay(ShiftedDay, paymentDay, calculationDay) )
import Language.Marlowe.ACTUS.BusinessEvents
    ( EventType(AD, IED, MD), projectEvent )
import Language.Marlowe.ACTUS.SCHED.ContractSchedule ( schedule )
import Language.Marlowe.ACTUS.INIT.StateInitialization
    ( inititializeState )
import Language.Marlowe.ACTUS.POF.Payoff ( payoff )
import Language.Marlowe.ACTUS.STF.StateTransition
    ( stateTransition )
import qualified Data.List as L ( zip, scanl, tail )
import Data.Maybe ( fromMaybe )
import Data.Time ( fromGregorian )



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


