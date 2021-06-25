{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.Utility.DateShift
  ( applyBDC
  , applyBDCWithCfg
  )
where

import qualified Data.List                                        as L
import           Data.Maybe                                       (fromJust)
import           Data.Time                                        (Day, addDays, toGregorian)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms (BDC (..), ScheduleConfig (..))
import           Language.Marlowe.ACTUS.Definitions.Schedule      (ShiftedDay (..))

{- Business Day Convention -}

applyBDCWithCfg :: ScheduleConfig -> Day -> ShiftedDay
applyBDCWithCfg ScheduleConfig {..} = applyBDC (fromJust bdc) calendar

applyBDC :: BDC -> [Day] -> Day -> ShiftedDay
applyBDC BDC_NULL _ date =
  ShiftedDay { paymentDay = date, calculationDay = date }

applyBDC BDC_SCF calendar date = ShiftedDay
  { paymentDay     = maybeShiftToFollowingBusinessDay date calendar
  , calculationDay = maybeShiftToFollowingBusinessDay date calendar
  }

applyBDC BDC_SCMF calendar date = ShiftedDay
  { paymentDay     = shiftModifiedFollowing date calendar
  , calculationDay = shiftModifiedFollowing date calendar
  }

applyBDC BDC_CSF calendar date = ShiftedDay
  { paymentDay     = maybeShiftToFollowingBusinessDay date calendar
  , calculationDay = date
  }

applyBDC BDC_CSMF calendar date = ShiftedDay
  { paymentDay     = shiftModifiedFollowing date calendar
  , calculationDay = date
  }

applyBDC BDC_SCP calendar date = ShiftedDay
  { paymentDay     = maybeShiftToPreceedingBusinessDay date calendar
  , calculationDay = maybeShiftToPreceedingBusinessDay date calendar
  }

applyBDC BDC_SCMP calendar date = ShiftedDay
  { paymentDay     = shiftModifiedPreceeding date calendar
  , calculationDay = shiftModifiedPreceeding date calendar
  }

applyBDC BDC_CSP calendar date = ShiftedDay
  { paymentDay     = maybeShiftToPreceedingBusinessDay date calendar
  , calculationDay = date
  }

applyBDC BDC_CSMP calendar date = ShiftedDay
  { paymentDay     = shiftModifiedPreceeding date calendar
  , calculationDay = date
  }


shiftModifiedFollowing :: Day -> [Day] -> Day
shiftModifiedFollowing date calendar =
  let (_, month, _)        = toGregorian date
      shiftedFollowing     = maybeShiftToFollowingBusinessDay date calendar
      (_, shiftedMonth, _) = toGregorian shiftedFollowing
  in  if month == shiftedMonth
        then shiftedFollowing
        else maybeShiftToPreceedingBusinessDay date calendar

shiftModifiedPreceeding :: Day -> [Day] -> Day
shiftModifiedPreceeding date calendar =
  let (_, month, _)        = toGregorian date
      shiftedPreceeding    = maybeShiftToPreceedingBusinessDay date calendar
      (_, shiftedMonth, _) = toGregorian shiftedPreceeding
  in  if month == shiftedMonth
        then shiftedPreceeding
        else maybeShiftToFollowingBusinessDay date calendar

maybeShiftToFollowingBusinessDay :: Day -> [Day] -> Day
maybeShiftToFollowingBusinessDay date calendar =
  let followingDay = addDays 1 date
      isHoliday dt = L.elem dt calendar
  in  if isHoliday date
        then maybeShiftToFollowingBusinessDay followingDay calendar
        else date


maybeShiftToPreceedingBusinessDay :: Day -> [Day] -> Day
maybeShiftToPreceedingBusinessDay date calendar =
  let preceedingDay = addDays (-1) date
      isHoliday dt = L.elem dt calendar
  in  if isHoliday date
        then maybeShiftToPreceedingBusinessDay preceedingDay calendar
        else date
