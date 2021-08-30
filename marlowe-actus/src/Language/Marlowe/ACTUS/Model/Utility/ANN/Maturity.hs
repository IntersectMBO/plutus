{-# LANGUAGE RecordWildCards #-}
module Language.Marlowe.ACTUS.Model.Utility.ANN.Maturity
  (maturity)
where

import           Data.Ord                                               (Down (..))
import           Data.Sort                                              (sortOn)
import           Data.Time                                              (Day)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms       (ContractTerms (..), Cycle (n), DCC,
                                                                         ScheduleConfig)
import           Language.Marlowe.ACTUS.Definitions.Schedule            (ShiftedDay (ShiftedDay, calculationDay, paymentDay),
                                                                         ShiftedSchedule)
import           Language.Marlowe.ACTUS.Model.Utility.DateShift         (applyBDCWithCfg)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator (generateRecurrentScheduleWithCorrections,
                                                                         plusCycle)
import           Language.Marlowe.ACTUS.Ops                             (YearFractionOps (_y))

maturity :: ContractTerms -> Maybe Day
maturity ContractTerms{..} =
  maturity'
    ct_SD
    ct_SD
    scfg
    ct_DCC
    ct_AD
    ct_MD
    ct_IED
    ct_PRANX
    ct_PRCL
    ct_PRNXT
    ct_IPNR
    ct_NT

maturity' :: Day            -- t0
          -> Day            -- status date
          -> ScheduleConfig -- schedule config
          -> Maybe DCC      -- day count convention
          -> Maybe Day      -- amorization date
          -> Maybe Day      -- maturity date
          -> Maybe Day      -- initial exchange date
          -> Maybe Day      -- cycle anchor date of principal redemption
          -> Maybe Cycle    -- cycle of principal redemption
          -> Maybe Double   -- next principal redemption payment
          -> Maybe Double   -- nominal interest rate
          -> Maybe Double   -- notional principal
          -> Maybe Day      -- maturity
maturity' t0 sd scfg (Just dcc) Nothing Nothing (Just ied) (Just pranx) (Just prcl) (Just prnxt) (Just ipnr) (Just nt) =
  let tplus = ied `plusCycle` prcl

      lastEvent
        | pranx >= t0 = pranx
        | tplus >= t0 = tplus
        | otherwise =
          let previousEvents = _S sd prcl pranx scfg
           in calculationDay . head . sortOn (Down . calculationDay) . filter (\ShiftedDay {..} -> calculationDay > t0) $ previousEvents

      timeFromLastEventPlusOneCycle = _y dcc lastEvent (lastEvent `plusCycle` prcl) Nothing

      redemptionPerCycle = prnxt - timeFromLastEventPlusOneCycle * ipnr * nt

      remainingPeriods = (ceiling (nt / redemptionPerCycle) - 1) :: Integer

   in Just . calculationDay . applyBDCWithCfg scfg $ lastEvent `plusCycle` prcl {n = remainingPeriods}

  where
    _S :: Day -> Cycle -> Day -> ScheduleConfig -> ShiftedSchedule
    _S = generateRecurrentScheduleWithCorrections

maturity' _ _ _ _ ad@(Just _) _ _ _ _ _ _ _        = ad
maturity' _ _ _ _ Nothing md@(Just _) _ _ _ _ _ _  = md
maturity' _ _ _ _ _ _ _ _ _ _ _ _                  = Nothing
