{-# LANGUAGE RecordWildCards #-}
module Language.Marlowe.ACTUS.Analysis(sampleCashflows, genProjectedCashflows, genZeroRiskAssertions) where

import qualified Data.List                                             as L (dropWhile, filter, find, groupBy, scanl,
                                                                             tail, zip)
import qualified Data.Map                                              as M (empty, fromList, lookup)
import           Data.Maybe                                            (fromJust, fromMaybe, isJust)
import           Data.Sort                                             (sortOn)
import           Data.Time                                             (Day)

import           Language.Marlowe                                      (Contract (Assert), Observation (..), Value (..))
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents     (DataObserved, EventType (..), RiskFactors (..),
                                                                        ValueObserved (..), ValuesObserved (..))
import           Language.Marlowe.ACTUS.Definitions.ContractState      (ContractState)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms      (Assertion (..), CT (..), ContractTerms (..))
import           Language.Marlowe.ACTUS.Definitions.Schedule           (CashFlow (..), ShiftedDay (..), calculationDay,
                                                                        paymentDay)
import           Language.Marlowe.ACTUS.MarloweCompat                  (constnt, useval)
import           Language.Marlowe.ACTUS.Model.INIT.StateInitialization (inititializeState)
import           Language.Marlowe.ACTUS.Model.POF.Payoff               (payoff)
import           Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule   (schedule)
import           Language.Marlowe.ACTUS.Model.STF.StateTransition      (stateTransition)
import           Language.Marlowe.ACTUS.Ops                            (ActusNum (..), YearFractionOps (_y))
import           Prelude                                               hiding (Fractional, Num, (*), (+), (-), (/))


genProjectedCashflows :: DataObserved -> ContractTerms -> [CashFlow]
genProjectedCashflows dataObserved = sampleCashflows dataObserved

postProcessSchedule :: ContractTerms -> [(EventType, ShiftedDay)] -> [(EventType, ShiftedDay)]
postProcessSchedule ct =
    let trim = L.dropWhile (\(_, d) -> calculationDay d < ct_SD ct)
        prioritised = [IED, FP, PR, PD, PRF, PY, PP, IP, IPCI, CE, RRF, RR, DV, PRD, MR, TD, SC, IPCB, MD, XD, STD, AD]
        priority :: (EventType, ShiftedDay) -> Integer
        priority (event, _) = fromJust $ M.lookup event $ M.fromList (zip prioritised [1..])
        simillarity (_, l) (_, r) = calculationDay l == calculationDay r
        regroup = L.groupBy simillarity
        overwrite = map (sortOn priority) . regroup
    in concat . (overwrite . trim)


sampleCashflows :: DataObserved -> ContractTerms -> [CashFlow]
sampleCashflows dataObserved terms =
    let
        eventTypes   = [IED, MD, RR, RRF, IP, PR, IPCB, IPCI, PRD, TD, SC]
        analysisDate = ct_SD terms

        preserveDate e d = (e, d)
        getSchedule e = fromMaybe [] $ schedule e terms
        scheduleEvent e = preserveDate e <$> getSchedule e
        events = sortOn (paymentDay . snd) $ concatMap scheduleEvent eventTypes
        events' = postProcessSchedule terms events

        events'' = filterEvents terms events'

        applyStateTransition (st, ev, date) (ev', date') =
            (stateTransition ev ((getRiskFactors dataObserved ev (calculationDay date) terms)) terms st (calculationDay date), ev', date')
        calculatePayoff (st, ev, date) =
            payoff ev ((getRiskFactors dataObserved ev (calculationDay date) terms)) terms st (calculationDay date)

        initialState =
            ( inititializeState terms
            , AD
            , ShiftedDay analysisDate analysisDate
            )
        states  = L.tail $ L.scanl applyStateTransition initialState events''

        states' = filterStates terms states

        payoffs = calculatePayoff <$> states'

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
        sortOn cashPaymentDay $ genCashflow <$> L.zip states' payoffs

filterEvents :: ContractTerms -> [(EventType, ShiftedDay)] -> [(EventType, ShiftedDay)]
filterEvents terms@ContractTerms{ contractType = contractType } events =
  case contractType of
    PAM ->
      if isJust (ct_TD terms) then
        L.filter (\(_, (ShiftedDay{ calculationDay = calculationDay })) -> calculationDay <= fromJust (ct_TD terms)) events
      else
        events
    LAM ->
      if isJust (ct_TD terms) then
        L.filter (\(_, (ShiftedDay{ calculationDay = calculationDay })) -> calculationDay <= fromJust (ct_TD terms)) events
      else
        events
    NAM ->
      if isJust (ct_TD terms) then
        L.filter (\(_, (ShiftedDay{ calculationDay = calculationDay })) -> calculationDay <= fromJust (ct_TD terms)) events
      else
        events

filterStates :: ContractTerms -> [(ContractState, EventType, ShiftedDay)] -> [(ContractState, EventType, ShiftedDay)]
filterStates terms@ContractTerms{ contractType = contractType } states =
  case contractType of
    PAM ->
      if isJust (ct_PRD terms) then
        L.filter (\(_, _, (ShiftedDay{ calculationDay = calculationDay })) -> calculationDay >= fromJust (ct_PRD terms)) states
      else
        states
    LAM ->
      if isJust (ct_PRD terms) then
        L.filter (\(_, eventType, (ShiftedDay{ calculationDay = calculationDay })) -> eventType == PRD || calculationDay > fromJust (ct_PRD terms)) states
      else
        states
    NAM ->
      if isJust (ct_PRD terms) then
        L.filter (\(_, eventType, (ShiftedDay{ calculationDay = calculationDay })) -> eventType == PRD || calculationDay > fromJust (ct_PRD terms)) states
      else
        states

genZeroRiskAssertions :: ContractTerms -> Assertion -> Contract -> Contract
genZeroRiskAssertions terms@ContractTerms{..} NpvAssertionAgainstZeroRiskBond{..} continue =
    let
        cfs = genProjectedCashflows (M.empty) terms

        dateToYearFraction :: Day -> Double
        dateToYearFraction dt = _y (fromJust ct_DCC) ct_SD dt ct_MD

        dateToDiscountFactor dt =  (1 - zeroRiskInterest) ** (dateToYearFraction dt)

        accumulateAndDiscount :: (Value Observation) -> (CashFlow, Integer) ->  (Value Observation)
        accumulateAndDiscount acc (cf, t) =
            let discountFactor = dateToDiscountFactor $ cashCalculationDay cf
                sign x = if (amount cf < 0.0) then (NegValue x) else x
            in (constnt discountFactor) * (sign $ useval "payoff" t) + acc
        npv = foldl accumulateAndDiscount (constnt 0) (zip cfs [1..])
    in Assert (ValueLT (constnt expectedNpv) npv) continue

getRiskFactors :: DataObserved -> EventType -> Day -> ContractTerms -> RiskFactors
getRiskFactors dataObserved ev date ContractTerms{..} =
  let riskFactors =
        RiskFactors {
          o_rf_CURS = 1.0
        , o_rf_RRMO = 1.0
        , o_rf_SCMO = 1.0
        , pp_payoff = 0.0
        }
      observedKey =
        case ev of
          RR ->
            ct_RRMO
          SC ->
            ct_SCMO
          _  ->
            ct_CURS
      value = fromMaybe 1.0 $ do observedKey' <- observedKey
                                 ValuesObserved{ values = values } <- M.lookup observedKey' dataObserved
                                 ValueObserved{ value = valueObserved } <-
                                   L.find (\ ValueObserved { timestamp = timestamp } -> timestamp == date) values
                                 return valueObserved
  in
    case ev of
      RR ->
        riskFactors { o_rf_RRMO = value }
      SC ->
        riskFactors { o_rf_SCMO = value }
      _  ->
        riskFactors { o_rf_CURS = value }
