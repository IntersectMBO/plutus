{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.Utility.DateShift
  ( applyBDC
  , applyBDCWithCfg
  )
where

import           Data.Time                                        (LocalTime (..), addDays, toGregorian)
import           Data.Time.Calendar.WeekDate                      (toWeekDate)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms (BDC (..), Calendar (..), ScheduleConfig (..))
import           Language.Marlowe.ACTUS.Definitions.Schedule      (ShiftedDay (..))

{- Business Day Convention -}

applyBDCWithCfg :: ScheduleConfig -> LocalTime -> ShiftedDay
applyBDCWithCfg
  ScheduleConfig
    { bdc = Just bdc',
      calendar = Just calendar'
    }
  d = applyBDC bdc' calendar' d
applyBDCWithCfg _ date = ShiftedDay {paymentDay = date, calculationDay = date}

applyBDC :: BDC -> Calendar -> LocalTime -> ShiftedDay
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

shiftModifiedFollowing :: LocalTime -> Calendar -> LocalTime
shiftModifiedFollowing lt@LocalTime {..} cal =
  let (_, month, _) = toGregorian localDay
      st@LocalTime {localDay = stLocalDay} = getFollowingBusinessDay lt cal
      (_, shiftedMonth, _) = toGregorian stLocalDay
   in if month == shiftedMonth then st else getPreceedingBusinessDay lt cal

shiftModifiedPreceeding :: LocalTime -> Calendar -> LocalTime
shiftModifiedPreceeding lt@LocalTime {..} cal =
  let (_, month, _) = toGregorian localDay
      st@LocalTime {localDay = stLocalDay} = getPreceedingBusinessDay lt cal
      (_, shiftedMonth, _) = toGregorian stLocalDay
   in if month == shiftedMonth then st else getFollowingBusinessDay lt cal

getFollowingBusinessDay :: LocalTime -> Calendar -> LocalTime
getFollowingBusinessDay LocalTime {..} CLDR_MF =
  let day = case toWeekDate localDay of
        (_, _, 6) -> addDays 2 localDay
        (_, _, 7) -> addDays 1 localDay
        _         -> localDay
   in LocalTime {localDay = day, localTimeOfDay = localTimeOfDay}
getFollowingBusinessDay lt _ = lt

getPreceedingBusinessDay :: LocalTime -> Calendar -> LocalTime
getPreceedingBusinessDay LocalTime {..} CLDR_MF =
  let day = case toWeekDate localDay of
        (_, _, 6) -> addDays (-1) localDay
        (_, _, 7) -> addDays (-2) localDay
        _         -> localDay
   in LocalTime {localDay = day, localTimeOfDay = localTimeOfDay}
getPreceedingBusinessDay lt _ = lt
