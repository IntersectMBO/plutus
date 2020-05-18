{-# LANGUAGE RecordWildCards #-}

{- This module contains cashflows that would happen without unscheduled events and risk factors -}

module Language.Marlowe.ACTUS.ProjectedCashFlows where

import Language.Marlowe.ACTUS.ContractTerms
import Language.Marlowe.ACTUS.Schedule
import Language.Marlowe.ACTUS.BusinessEvents
import Language.Marlowe.ACTUS.SCHED.ContractSchedule
import Language.Marlowe.ACTUS.INIT.StateInitialization
import Language.Marlowe.ACTUS.POF.Payoff
import Language.Marlowe.ACTUS.STF.StateTransition
import Data.List
import qualified Data.List as L
import Data.Maybe
import Data.Time


genProjectedCashflows :: ContractTerms -> [CashFlow]
genProjectedCashflows terms = let
    eventTypes = [IED, MD]
    analysisDate = fromGregorian 2008 10 22

    projectPreserveDate e d = ((projectEvent e), d)
    getSchedule e = fromMaybe [] $ schedule e terms
    scheduleEvent e = fmap (projectPreserveDate e) (getSchedule e)
    events = concatMap scheduleEvent eventTypes

    applyStateTransition (st, _, _) (ev, date) = (stateTransition ev terms st (calculationDay date) undefined undefined, ev, date)
    calculatePayoff (st, ev, date) = payoff ev terms st (calculationDay date) undefined undefined

    init = (inititializeState terms, (projectEvent AD), ShiftedDay analysisDate analysisDate)
    states = L.scanl applyStateTransition init events
    payoffs = L.map calculatePayoff states

    genCashflow ((ev, d), payoff) = CashFlow {
        tick = 0,
        cashContractId = "0",
        cashParty = "party",
        cashCounterParty = "counterparty",
        cashPaymentDay = paymentDay d,
        cashCalculationDay = calculationDay d,
        cashEvent = ev,
        amount = payoff,
        currency = "ada"
    }
    in L.map genCashflow $ L.zip events payoffs



