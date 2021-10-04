{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections   #-}

{-| = ACTUS Analysis

Given ACTUS contract terms cashflows can be projected from the predefined risk factors.
The cash flows can be used to generate the payments in a Marlowe contract.

-}

module Language.Marlowe.ACTUS.Analysis
  ( genProjectedCashflows
  , genProjectedPayoffs
  )
where

import           Control.Applicative                                        ((<|>))
import           Control.Monad.Reader                                       (runReader)
import           Data.Functor                                               ((<&>))
import qualified Data.List                                                  as L (groupBy)
import           Data.Maybe                                                 (isNothing)
import           Data.Sort                                                  (sortOn)
import           Data.Time                                                  (LocalTime)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents          (EventType (..), RiskFactors)
import           Language.Marlowe.ACTUS.Definitions.ContractState           (ContractState)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms           (CT (..), ContractTerms,
                                                                             ContractTermsPoly (..))
import           Language.Marlowe.ACTUS.Definitions.Schedule                (CashFlow (..), ShiftedDay (..),
                                                                             calculationDay, paymentDay)
import           Language.Marlowe.ACTUS.Model.INIT.StateInitializationModel (initializeState)
import           Language.Marlowe.ACTUS.Model.POF.Payoff                    (payoff)
import           Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule        as S (maturity, schedule)
import           Language.Marlowe.ACTUS.Model.STF.StateTransition           (CtxSTF (..), stateTransition)

-- |'genProjectedCashflows' generates a list of projected cashflows for
-- given contract terms and provided risk factors. The function returns
-- an empty list, if building the initial state given the contract terms
-- fails or in case there are no cash flows.
genProjectedCashflows ::
  (EventType -> LocalTime -> RiskFactors) -- ^ Risk factors as a function of event type and time
  -> ContractTerms                        -- ^ ACTUS contract terms
  -> [CashFlow]                           -- ^ List of projected cash flows
genProjectedCashflows getRiskFactors =
  let genCashflow ((_, ev, t), am) =
        CashFlow
          { tick = 0,
            cashContractId = "0",
            cashParty = "party",
            cashCounterParty = "counterparty",
            cashPaymentDay = paymentDay t,
            cashCalculationDay = calculationDay t,
            cashEvent = ev,
            amount = am,
            currency = "ada"
          }
   in sortOn cashPaymentDay . fmap genCashflow . genProjectedPayoffs getRiskFactors

genProjectedPayoffs ::
  (EventType -> LocalTime -> RiskFactors)               -- ^ Risk factors as a function of event type and time
  -> ContractTerms                                      -- ^ ACTUS contract terms
  -> [((ContractState, EventType, ShiftedDay), Double)] -- ^ List of projected payoffs
genProjectedPayoffs getRiskFactors ct@ContractTermsPoly {..} =
  let -- schedules

      schedules =
        filter filtersSchedules . postProcessSchedule . sortOn (paymentDay . snd) $
          concatMap scheduleEvent eventTypes
        where
          eventTypes = [IED, MD, RR, RRF, IP, PR, PRF, IPCB, IPCI, PRD, TD, SC]
          scheduleEvent ev = (ev,) <$> schedule ev ct

      -- states

      states =
        filter filtersStates . tail $
          runReader (sequence $ scanl applyStateTransition initialState schedules) context
        where
          initialState = initializeState <&> (,AD,ShiftedDay ct_SD ct_SD)

          applyStateTransition x (ev', t') = do
            (st, ev, d) <- x
            let t = calculationDay d
            let rf = getRiskFactors ev t
            stateTransition ev rf t st <&> (,ev',t')

          context = CtxSTF ct fpSchedule prSchedule ipSchedule mat

          fpSchedule = calculationDay <$> schedule FP ct -- init & stf rely on the fee payment schedule
          prSchedule = calculationDay <$> schedule PR ct -- init & stf rely on the principal redemption schedule
          ipSchedule = calculationDay <$> schedule IP ct -- init & stf rely on the interest payment schedule

      -- payoffs

      payoffs = calculatePayoff <$> states
        where
          calculatePayoff (st, ev, d) =
            let t = calculationDay d
                rf = getRiskFactors ev t
             in payoff ev rf ct st t
   in zip states payoffs
  where
    mat = S.maturity ct

    filtersSchedules :: (EventType, ShiftedDay) -> Bool
    filtersSchedules (_, ShiftedDay {..}) = isNothing ct_TD || Just calculationDay <= ct_TD

    filtersStates :: (ContractState, EventType, ShiftedDay) -> Bool
    filtersStates (_, ev, ShiftedDay {..}) =
      case contractType of
        PAM -> isNothing ct_PRD || Just calculationDay >= ct_PRD
        LAM -> isNothing ct_PRD || ev == PRD || Just calculationDay > ct_PRD
        NAM -> isNothing ct_PRD || ev == PRD || Just calculationDay > ct_PRD
        ANN ->
          let b1 = isNothing ct_PRD || ev == PRD || Just calculationDay > ct_PRD
              b2 = let m = ct_MD <|> ct_AD <|> mat in isNothing m || Just calculationDay <= m
           in b1 && b2

    postProcessSchedule :: [(EventType, ShiftedDay)] -> [(EventType, ShiftedDay)]
    postProcessSchedule =
      let trim = dropWhile (\(_, d) -> calculationDay d < ct_SD)

          priority :: (EventType, ShiftedDay) -> Int
          priority (event, _) = fromEnum event

          similarity (_, l) (_, r) = calculationDay l == calculationDay r
          regroup = L.groupBy similarity

          overwrite = map (sortOn priority) . regroup
       in concat . overwrite . trim
