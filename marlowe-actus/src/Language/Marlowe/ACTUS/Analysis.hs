{-# LANGUAGE RecordWildCards #-}
module Language.Marlowe.ACTUS.Analysis(sampleCashflows, genProjectedCashflows, genZeroRiskAssertions) where

import qualified Data.List                                             as L (scanl, tail, zip, dropWhile, groupBy, head)
import           Data.Maybe                                            (fromJust, fromMaybe)
import           Data.Sort                                             (sortOn)
import           Data.Time                                             (Day, fromGregorian)

import           Language.Marlowe                                      (Contract (Assert), Observation (..), Value (..))
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents     (EventType (..), RiskFactors (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms      (Assertion (..), ContractTerms (..))
import           Language.Marlowe.ACTUS.Definitions.Schedule           (CashFlow (..), ShiftedDay (..), calculationDay,
                                                                        paymentDay)
import           Language.Marlowe.ACTUS.MarloweCompat                  (constnt, useval)
import           Language.Marlowe.ACTUS.Model.INIT.StateInitialization (inititializeState)
import           Language.Marlowe.ACTUS.Model.POF.Payoff               (payoff)
import           Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule   (schedule)
import           Language.Marlowe.ACTUS.Model.STF.StateTransition      (stateTransition)
import           Language.Marlowe.ACTUS.Ops                            (ActusNum (..), YearFractionOps (_y))
import           Prelude                                               hiding (Fractional, Num, (*), (+), (-), (/))


genProjectedCashflows :: ContractTerms -> [CashFlow]
genProjectedCashflows = sampleCashflows (const $ RiskFactors 1.0 1.0 1.0 0.0)

postProcessSchedule :: ContractTerms -> [(EventType, ShiftedDay)] -> [(EventType, ShiftedDay)]
postProcessSchedule ct s = 
    let trim = L.dropWhile (\(_, d) -> calculationDay d < ct_SD ct)

        priority (event, _) = 1
        regroup = L.groupBy (\((_, l), (_, r)) -> calculationDay l == calculationDay r)
        overwrite = L.head . sortOn priority <$> regroup
    in (overwrite . trim) s


sampleCashflows :: (Day -> RiskFactors) -> ContractTerms -> [CashFlow]
sampleCashflows riskFactors terms =
    let
        eventTypes   = [IED, MD, RR, IP, PR, IPCB]
        analysisDate = fromGregorian 1970 1 1

        preserveDate e d = (e, d)
        getSchedule e = fromMaybe [] $ schedule e terms
        scheduleEvent e = preserveDate e <$> getSchedule e
        events = sortOn (paymentDay . snd) $ concatMap scheduleEvent eventTypes
        events' = postProcessSchedule terms events
        
        applyStateTransition (st, ev, date) (ev', date') =
            (stateTransition ev (riskFactors $ calculationDay date) terms st (calculationDay date), ev', date')
        calculatePayoff (st, ev, date) =
            payoff ev (riskFactors $ calculationDay date) terms st (calculationDay date)

        initialState =
            ( inititializeState terms
            , AD
            , ShiftedDay analysisDate analysisDate
            )
        states  = L.tail $ L.scanl applyStateTransition initialState events'
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

genZeroRiskAssertions :: ContractTerms -> Assertion -> Contract -> Contract
genZeroRiskAssertions terms@ContractTerms{..} NpvAssertionAgainstZeroRiskBond{..} continue =
    let
        cfs = genProjectedCashflows terms

        dateToYearFraction :: Day -> Double
        dateToYearFraction dt = _y ct_DCC ct_SD dt (fromJust ct_MD)

        dateToDiscountFactor dt =  (1 - zeroRiskInterest) ** (dateToYearFraction dt)

        accumulateAndDiscount :: (Value Observation) -> (CashFlow, Integer) ->  (Value Observation)
        accumulateAndDiscount acc (cf, t) =
            let discountFactor = dateToDiscountFactor $ cashCalculationDay cf
                sign x = if (amount cf < 0.0) then (NegValue x) else x
            in (constnt discountFactor) * (sign $ useval "payoff" t) + acc
        npv = foldl accumulateAndDiscount (constnt 0) (zip cfs [1..])
    in Assert (ValueLT (constnt expectedNpv) npv) continue
