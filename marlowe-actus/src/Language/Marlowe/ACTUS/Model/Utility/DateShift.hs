

module Language.Marlowe.ACTUS.Model.Utility.DateShift
  ( applyBDC
  , applyBDCWithCfg
  )
where

import           Data.Time                                        (Day, addDays, toGregorian)
import           Data.Time.Calendar.WeekDate                      (toWeekDate)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms (BDC (..), Calendar (..), ScheduleConfig (..))
import           Language.Marlowe.ACTUS.Definitions.Schedule      (ShiftedDay (..))

{- Business Day Convention -}

applyBDCWithCfg :: ScheduleConfig -> Day -> ShiftedDay
applyBDCWithCfg
  ScheduleConfig
    { bdc = Just bdc',
      calendar = Just calendar'
    }
  d = applyBDC bdc' calendar' d
applyBDCWithCfg _ date = ShiftedDay {paymentDay = date, calculationDay = date}

applyBDC :: BDC -> Calendar -> Day -> ShiftedDay
applyBDC BDC_NULL _ date =
  ShiftedDay { paymentDay = date, calculationDay = date }

applyBDC BDC_SCF cal date = ShiftedDay
  { paymentDay     = getFollowingBusinessDay date cal
  , calculationDay = getFollowingBusinessDay date cal
  }

applyBDC BDC_SCMF cal date = ShiftedDay
  { paymentDay     = shiftModifiedFollowing date cal
  , calculationDay = shiftModifiedFollowing date cal
  }

applyBDC BDC_CSF cal date = ShiftedDay
  { paymentDay     = getFollowingBusinessDay date cal
  , calculationDay = date
  }

applyBDC BDC_CSMF cal date = ShiftedDay
  { paymentDay     = shiftModifiedFollowing date cal
  , calculationDay = date
  }

applyBDC BDC_SCP cal date = ShiftedDay
  { paymentDay     = getPreceedingBusinessDay date cal
  , calculationDay = getPreceedingBusinessDay date cal
  }

applyBDC BDC_SCMP cal date = ShiftedDay
  { paymentDay     = shiftModifiedPreceeding date cal
  , calculationDay = shiftModifiedPreceeding date cal
  }

applyBDC BDC_CSP cal date = ShiftedDay
  { paymentDay     = getPreceedingBusinessDay date cal
  , calculationDay = date
  }

applyBDC BDC_CSMP cal date = ShiftedDay
  { paymentDay     = shiftModifiedPreceeding date cal
  , calculationDay = date
  }


shiftModifiedFollowing :: Day -> Calendar -> Day
shiftModifiedFollowing date cal =
  let (_, month, _)        = toGregorian date
      shiftedFollowing     = getFollowingBusinessDay date cal
      (_, shiftedMonth, _) = toGregorian shiftedFollowing
  in  if month == shiftedMonth
        then shiftedFollowing
        else getPreceedingBusinessDay date cal

shiftModifiedPreceeding :: Day -> Calendar -> Day
shiftModifiedPreceeding date cal =
  let (_, month, _)        = toGregorian date
      shiftedPreceeding    = getPreceedingBusinessDay date cal
      (_, shiftedMonth, _) = toGregorian shiftedPreceeding
  in  if month == shiftedMonth
        then shiftedPreceeding
        else getFollowingBusinessDay date cal

getFollowingBusinessDay :: Day -> Calendar -> Day
getFollowingBusinessDay date cal =
  case cal of
    CLDR_MF ->
      case toWeekDate date of
        (_, _, 6) ->
          addDays 2 date
        (_, _, 7) ->
          addDays 1 date
        _ ->
          date
    CLDR_NC ->
      date

getPreceedingBusinessDay :: Day -> Calendar -> Day
getPreceedingBusinessDay date cal =
  case cal of
    CLDR_MF ->
      case toWeekDate date of
        (_, _, 6) ->
          addDays (-1) date
        (_, _, 7) ->
          addDays (-2) date
        _ ->
          date
    CLDR_NC ->
      date
