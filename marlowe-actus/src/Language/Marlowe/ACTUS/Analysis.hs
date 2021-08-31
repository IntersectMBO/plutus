{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections   #-}
module Language.Marlowe.ACTUS.Analysis
  (genProjectedCashflows)
where

import           Control.Applicative                                   (Alternative ((<|>)))
import qualified Data.List                                             as L (dropWhile, find, groupBy, scanl, tail, zip)
import qualified Data.Map                                              as M (fromList, lookup)
import           Data.Maybe                                            (fromJust, fromMaybe, isNothing)
import           Data.Sort                                             (sortOn)
import           Data.Time                                             (Day)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents     (DataObserved, EventType (..), RiskFactors (..),
                                                                        ValueObserved (..), ValuesObserved (..))
import           Language.Marlowe.ACTUS.Definitions.ContractState      (ContractState)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms      (CT (..), ContractTerms (..))
import           Language.Marlowe.ACTUS.Definitions.Schedule           (CashFlow (..), ShiftedDay (..), calculationDay,
                                                                        paymentDay)
import           Language.Marlowe.ACTUS.Model.INIT.StateInitialization (initializeState)
import           Language.Marlowe.ACTUS.Model.POF.Payoff               (payoff)
import           Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule   (schedule)
import           Language.Marlowe.ACTUS.Model.STF.StateTransition      (stateTransition)
import           Language.Marlowe.ACTUS.Model.Utility.ANN.Maturity     (maturity)

genProjectedCashflows :: DataObserved -> ContractTerms -> [CashFlow]
genProjectedCashflows dataObserved ct@ContractTerms {..} =
  let -- schedule
      scheduleEvent e = maybe [] (fmap (e,)) (schedule e ct)

      -- events
      eventTypes = [IED, MD, RR, RRF, IP, PR, PRF, IPCB, IPCI, PRD, TD, SC]

      events =
        let e = concatMap scheduleEvent eventTypes
         in filter filtersEvents . postProcessSchedule . sortOn (paymentDay . snd) $ e

      -- states
      applyStateTransition (st, ev, date) (ev', date') =
        let t = calculationDay date
            rf = getRiskFactors ev t
         in (stateTransition ev rf ct st t, ev', date')

      states =
        let initialState = (initializeState ct, AD, ShiftedDay ct_SD ct_SD)
         in filter filtersStates $ L.tail $ L.scanl applyStateTransition initialState events

      -- payoff
      calculatePayoff (st, ev, date) =
        let t = calculationDay date
            rf = getRiskFactors ev t
         in payoff ev rf ct st t

      payoffs = calculatePayoff <$> states

      genCashflow ((_, ev, d), pff) =
        CashFlow
          { tick = 0,
            cashContractId = "0",
            cashParty = "party",
            cashCounterParty = "counterparty",
            cashPaymentDay = paymentDay d,
            cashCalculationDay = calculationDay d,
            cashEvent = ev,
            amount = pff,
            currency = "ada"
          }

   in sortOn cashPaymentDay $ genCashflow <$> L.zip states payoffs

  where

    filtersEvents :: (EventType, ShiftedDay) -> Bool
    filtersEvents (_, ShiftedDay {..}) = isNothing ct_TD || Just calculationDay <= ct_TD

    filtersStates :: (ContractState, EventType, ShiftedDay) -> Bool
    filtersStates (_, ev, ShiftedDay {..}) =
      case contractType of
        PAM -> isNothing ct_PRD || Just calculationDay >= ct_PRD
        LAM -> isNothing ct_PRD || ev == PRD || Just calculationDay > ct_PRD
        NAM -> isNothing ct_PRD || ev == PRD || Just calculationDay > ct_PRD
        ANN ->
          let b1 = isNothing ct_PRD || ev == PRD || Just calculationDay > ct_PRD
              b2 = let m = ct_MD <|> ct_AD <|> maturity ct in isNothing m || Just calculationDay <= m
           in b1 && b2

    postProcessSchedule :: [(EventType, ShiftedDay)] -> [(EventType, ShiftedDay)]
    postProcessSchedule =
      let trim = L.dropWhile (\(_, d) -> calculationDay d < ct_SD)
          prioritised = [IED, FP, PR, PD, PY, PP, IP, IPCI, CE, RRF, RR, PRF, DV, PRD, MR, TD, SC, IPCB, MD, XD, STD, AD]

          priority :: (EventType, ShiftedDay) -> Integer
          priority (event, _) = fromJust $ M.lookup event $ M.fromList (zip prioritised [1 ..])

          similarity (_, l) (_, r) = calculationDay l == calculationDay r
          regroup = L.groupBy similarity

          overwrite = map (sortOn priority) . regroup
       in concat . (overwrite . trim)

    getRiskFactors :: EventType -> Day -> RiskFactors
    getRiskFactors ev date =
      let riskFactors =
            RiskFactors
              { o_rf_CURS = 1.0,
                o_rf_RRMO = 1.0,
                o_rf_SCMO = 1.0,
                pp_payoff = 0.0
              }

          observedKey RR = ct_RRMO
          observedKey SC = ct_SCMO
          observedKey _  = ct_CURS

          value = fromMaybe 1.0 $ do
            k <- observedKey ev
            ValuesObserved {values = values} <- M.lookup k dataObserved
            ValueObserved {value = valueObserved} <- L.find (\ValueObserved {timestamp = timestamp} -> timestamp == date) values
            return valueObserved
       in case ev of
            RR -> riskFactors {o_rf_RRMO = value}
            SC -> riskFactors {o_rf_SCMO = value}
            _  -> riskFactors {o_rf_CURS = value}
