{-# LANGUAGE RecordWildCards #-}
module Language.Marlowe.ACTUS.Analysis(genProjectedCashflows, genZeroRiskAssertions) where

import           Data.Time                                               (Day, fromGregorian)
import qualified Data.List                                               as L (scanl, tail, zip)
import           Data.Maybe                                              (fromMaybe)
import           Data.Sort                                               (sortOn)   

import           Language.Marlowe                                        (Contract(Assert), Value(..), Observation(..))
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents       (EventType (..), RiskFactors (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms        (ContractTerms(..))
import           Language.Marlowe.ACTUS.Definitions.Schedule             (CashFlow (..), ShiftedDay (..),
                                                                          calculationDay, paymentDay)
import           Language.Marlowe.ACTUS.MarloweCompat                    (constnt, useval)
import           Language.Marlowe.ACTUS.Model.INIT.StateInitialization   (inititializeState)
import           Language.Marlowe.ACTUS.Model.POF.Payoff                 (payoff)
import           Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule     (schedule)
import           Language.Marlowe.ACTUS.Model.STF.StateTransition        (stateTransition)
import           Language.Marlowe.ACTUS.Ops                       (ActusNum (..), YearFractionOps (_y))
import           Prelude                                          hiding (Fractional, Num, (*), (+), (-), (/))

genProjectedCashflows :: ContractTerms -> [CashFlow]
genProjectedCashflows terms =
    let
        eventTypes   = [IED, MD, RR, IP]
        analysisDate = fromGregorian 2008 10 22
        riskFactors = RiskFactors 1.0 1.0 1.0 1.0 analysisDate

        preserveDate e d = (e, d)
        getSchedule e = fromMaybe [] $ schedule e terms
        scheduleEvent e = preserveDate e <$> getSchedule e
        events = concatMap scheduleEvent eventTypes

        applyStateTransition (st, ev, date) (ev', date') =
            (stateTransition ev riskFactors terms st (calculationDay date), ev', date')
        calculatePayoff (st, ev, date) =
            payoff ev riskFactors terms st (calculationDay date)

        initialState =
            ( inititializeState terms
            , AD
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
        sortOn cashPaymentDay $ genCashflow <$> L.zip states payoffs

genZeroRiskAssertions :: Double -> Double -> ContractTerms -> Contract -> Contract
genZeroRiskAssertions zeroRiskInterest threshold terms@ContractTerms{..} continue = 
    let
        cfs = genProjectedCashflows terms

        dateToYearFraction :: Day -> Double
        dateToYearFraction dt = _y ct_DCC ct_SD dt ct_MD

        dateToDiscountFactor dt =  (1 - zeroRiskInterest) ** (dateToYearFraction dt)

        accumulateAndDiscount :: (Value Observation) -> (CashFlow, Integer) ->  (Value Observation)
        accumulateAndDiscount acc (cf, t) = 
            let discountFactor = dateToDiscountFactor $ cashCalculationDay cf
                sign x = if (amount cf < 0.0) then (NegValue x) else x
            in (constnt discountFactor) * (sign $ useval "payoff" t) + acc --todo plus vs minus
        npv = foldl accumulateAndDiscount (constnt 0) (zip cfs [1..])
    in Assert (ValueLT (constnt threshold) npv) continue
