{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.Utility.DateShift
  ( applyBDC
  , applyBDCWithCfg
  )
where

import Data.Time ( Day, toGregorian, addDays )
import Language.Marlowe.ACTUS.Definitions.ContractTerms
    ( ScheduleConfig(..), Calendar, BDC(..) )
import Language.Marlowe.ACTUS.Definitions.Schedule ( ShiftedDay(..) )


{- Business Day Convention -}

applyBDCWithCfg :: ScheduleConfig -> Day -> ShiftedDay
applyBDCWithCfg ScheduleConfig {..} = applyBDC bdc calendar

applyBDC :: BDC -> Calendar -> Day -> ShiftedDay
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


shiftModifiedFollowing :: Day -> Calendar -> Day
shiftModifiedFollowing date calendar =
  let (_, month, _)        = toGregorian date
      shiftedFollowing     = maybeShiftToFollowingBusinessDay date calendar
      (_, shiftedMonth, _) = toGregorian shiftedFollowing
  in  if month == shiftedMonth
        then shiftedFollowing
        else maybeShiftToPreceedingBusinessDay date calendar

shiftModifiedPreceeding :: Day -> Calendar -> Day
shiftModifiedPreceeding date calendar =
  let (_, month, _)        = toGregorian date
      shiftedPreceeding    = maybeShiftToPreceedingBusinessDay date calendar
      (_, shiftedMonth, _) = toGregorian shiftedPreceeding
  in  if month == shiftedMonth
        then shiftedPreceeding
        else maybeShiftToFollowingBusinessDay date calendar

maybeShiftToFollowingBusinessDay :: Day -> Calendar -> Day
maybeShiftToFollowingBusinessDay date isHoliday =
  let followingDay = addDays 1 date
  in  if isHoliday date
        then maybeShiftToFollowingBusinessDay followingDay isHoliday
        else date


maybeShiftToPreceedingBusinessDay :: Day -> Calendar -> Day
maybeShiftToPreceedingBusinessDay date isHoliday =
  let preceedingDay = addDays (-1) date
  in  if isHoliday date
        then maybeShiftToPreceedingBusinessDay preceedingDay isHoliday
        else date

