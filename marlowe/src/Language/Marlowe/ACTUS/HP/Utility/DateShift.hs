module Language.Marlowe.ACTUS.HP.Utility.DateShift(applyBDC) where

import Debug.Trace

import Data.List as List
import Data.Time
import Data.Time.Calendar

import Language.Marlowe.ACTUS.HP.ContractTerms
import Language.Marlowe.ACTUS.HP.Schedule

{- Business Day Convention -}
applyBDC :: Day -> BDC -> Calendar -> ShiftedDay
applyBDC date BDC_NULL _ =
  ShiftedDay {
    paymentDay = date, 
    calculationDay = date
  }

applyBDC date BDC_SCF calendar =
  ShiftedDay {
    paymentDay = maybeShiftToFollowingBusinessDay date calendar, 
    calculationDay = maybeShiftToFollowingBusinessDay date calendar
  }
  
applyBDC date BDC_SCMF calendar =
  ShiftedDay {
    paymentDay = shiftModifiedFollowing date calendar, 
    calculationDay = shiftModifiedFollowing date calendar
  }

applyBDC date BDC_CSF calendar =
  ShiftedDay {
    paymentDay = maybeShiftToFollowingBusinessDay date calendar, 
    calculationDay = date
  }

applyBDC date BDC_CSMF calendar =
  ShiftedDay {
    paymentDay = shiftModifiedFollowing date calendar, 
    calculationDay = date
  }

applyBDC date BDC_SCP calendar =
  ShiftedDay {
    paymentDay = maybeShiftToPreceedingBusinessDay date calendar, 
    calculationDay = maybeShiftToPreceedingBusinessDay date calendar
  }

applyBDC date BDC_SCMP calendar =
  ShiftedDay {
    paymentDay = shiftModifiedPreceeding date calendar, 
    calculationDay = shiftModifiedPreceeding date calendar
  }

applyBDC date BDC_CSP calendar =
  ShiftedDay {
    paymentDay = maybeShiftToPreceedingBusinessDay date calendar, 
    calculationDay = date
  }

applyBDC date BDC_CSMP calendar =
  ShiftedDay {
    paymentDay = shiftModifiedPreceeding date calendar, 
    calculationDay = date
  }


shiftModifiedFollowing :: Day -> Calendar -> Day
shiftModifiedFollowing date calendar =
  let (_, month, _) = toGregorian date
      shiftedFollowing = maybeShiftToFollowingBusinessDay date calendar
      (_, shiftedMonth, _) = toGregorian shiftedFollowing
  in
    if month == shiftedMonth then shiftedFollowing
    else maybeShiftToPreceedingBusinessDay date calendar

shiftModifiedPreceeding :: Day -> Calendar -> Day
shiftModifiedPreceeding date calendar =
  let (_, month, _) = toGregorian date
      shiftedPreceeding = maybeShiftToPreceedingBusinessDay date calendar
      (_, shiftedMonth, _) = toGregorian shiftedPreceeding
  in
    if month == shiftedMonth then shiftedPreceeding
    else maybeShiftToFollowingBusinessDay date calendar

maybeShiftToFollowingBusinessDay :: Day -> Calendar -> Day
maybeShiftToFollowingBusinessDay date isHoliday = 
  let followingDay = addDays 1 date in
  if isHoliday date then maybeShiftToFollowingBusinessDay followingDay isHoliday else date
  

maybeShiftToPreceedingBusinessDay :: Day -> Calendar -> Day
maybeShiftToPreceedingBusinessDay date isHoliday = 
  let preceedingDay = addDays (-1) date in
  if isHoliday date then maybeShiftToPreceedingBusinessDay preceedingDay isHoliday else date
  