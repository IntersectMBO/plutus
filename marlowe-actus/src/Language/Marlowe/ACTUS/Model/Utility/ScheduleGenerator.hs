{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator
  ( generateRecurrentScheduleWithCorrections
  , (<+>)
  , (<->)
  , sup
  , inf
  , sup'
  , inf'
  , remove
  , applyEOMC
  , moveToEndOfMonth
  )
where

import qualified Data.List                                        as L (delete, init, last, length)
import           Data.Time                                        (LocalTime (..))
import           Data.Time.Calendar                               (addDays, addGregorianMonthsClip,
                                                                   addGregorianYearsClip, fromGregorian,
                                                                   gregorianMonthLength, toGregorian)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms (Cycle (..), EOMC (EOMC_EOM), Period (..),
                                                                   ScheduleConfig (..), Stub (LongStub))
import           Language.Marlowe.ACTUS.Definitions.Schedule      (ShiftedDay (..), ShiftedSchedule)
import           Language.Marlowe.ACTUS.Model.Utility.DateShift   (applyBDC)

maximumMaybe :: Ord a => [a] -> Maybe a
maximumMaybe [] = Nothing
maximumMaybe xs = Just $ maximum xs

minimumMaybe :: Ord a => [a] -> Maybe a
minimumMaybe [] = Nothing
minimumMaybe xs = Just $ minimum xs

inf :: [ShiftedDay] -> LocalTime -> Maybe ShiftedDay
inf set threshold =
  minimumMaybe [t | t <- set, calculationDay t > threshold]

sup :: [ShiftedDay] -> LocalTime -> Maybe ShiftedDay
sup set threshold =
  maximumMaybe [t | t <- set, calculationDay t < threshold]

inf' :: (Ord a) => [a] -> a -> Maybe a
inf' set threshold =
  minimumMaybe [t | t <- set, t > threshold]

sup' :: (Ord a) => [a] -> a -> Maybe a
sup' set threshold =
  maximumMaybe [t | t <- set, t < threshold]

remove :: ShiftedDay -> [ShiftedDay] -> [ShiftedDay]
remove d = filter (\t -> calculationDay t /= calculationDay d)

correction :: Cycle -> LocalTime -> LocalTime -> [LocalTime] -> [LocalTime]
correction Cycle{ stub = stub, includeEndDay = includeEndDay} anchorDate endDate schedule =
  let
    lastDate = L.last schedule
    schedule' = L.init schedule
    scheduleSize = L.length schedule'
    schedule'' =
      if not includeEndDay && endDate == anchorDate then
        L.delete anchorDate schedule'
      else
        schedule'
  in
    if stub == LongStub && L.length schedule'' > 2 && endDate /= lastDate then
      L.delete (schedule'' !! (scheduleSize - 1)) schedule''
    else
      schedule''

addEndDay :: Bool -> LocalTime -> ShiftedSchedule -> ShiftedSchedule
addEndDay includeEndDay endDate schedule =
  if includeEndDay then
    schedule ++ [ShiftedDay{ calculationDay = endDate, paymentDay = endDate }]
  else
    schedule

generateRecurrentSchedule :: Cycle -> LocalTime -> LocalTime -> [LocalTime]
generateRecurrentSchedule Cycle {..} anchorDate endDate =
  let go :: LocalTime -> Integer -> [LocalTime] -> [LocalTime]
      go current k acc = if current >= endDate || n == 0
        then acc ++ [current]
        else let current' = shiftDate anchorDate (k * n) p
              in  go current' (k + 1) (acc ++ [current])

  in  go anchorDate 1 []

generateRecurrentScheduleWithCorrections :: LocalTime -> Cycle -> LocalTime -> ScheduleConfig -> ShiftedSchedule
generateRecurrentScheduleWithCorrections
  anchorDate
  cycle
  endDate
  ScheduleConfig
    { eomc = Just eomc',
      calendar = Just calendar',
      bdc = Just bdc'
    } =
      let s = generateRecurrentSchedule cycle anchorDate endDate
          c = correction cycle anchorDate endDate s
        in addEndDay (includeEndDay cycle) endDate $ fmap (applyBDC bdc' calendar' . applyEOMC anchorDate cycle eomc') c
generateRecurrentScheduleWithCorrections _ _ _ _ = []

plusCycle :: LocalTime -> Cycle -> LocalTime
plusCycle date cycle = shiftDate date (n cycle) (p cycle)

minusCycle :: LocalTime -> Cycle -> LocalTime
minusCycle date cycle = shiftDate date (-n cycle) (p cycle)

(<+>) :: LocalTime -> Cycle -> LocalTime
(<+>) = plusCycle

(<->) :: LocalTime -> Cycle -> LocalTime
(<->) = minusCycle

shiftDate :: LocalTime -> Integer -> Period -> LocalTime
shiftDate LocalTime {..} n p = case p of
  P_D -> LocalTime {localDay = addDays n localDay, localTimeOfDay = localTimeOfDay}
  P_W -> LocalTime {localDay = addDays (n * 7) localDay, localTimeOfDay = localTimeOfDay}
  P_M -> LocalTime {localDay = addGregorianMonthsClip n localDay, localTimeOfDay = localTimeOfDay}
  P_Q -> LocalTime {localDay = addGregorianMonthsClip (n * 3) localDay, localTimeOfDay = localTimeOfDay}
  P_H -> LocalTime {localDay = addGregorianMonthsClip (n * 6) localDay, localTimeOfDay = localTimeOfDay}
  P_Y -> LocalTime {localDay = addGregorianYearsClip n localDay, localTimeOfDay = localTimeOfDay}

{- End of Month Convention -}
applyEOMC :: LocalTime -> Cycle -> EOMC -> LocalTime -> LocalTime
applyEOMC s Cycle {..} endOfMonthConvention date
  | isLastDayOfMonthWithLessThan31Days s
    && p /= P_D
    && p /= P_W
    && endOfMonthConvention == EOMC_EOM
  = moveToEndOfMonth date
  | otherwise
  = date

isLastDayOfMonthWithLessThan31Days :: LocalTime -> Bool
isLastDayOfMonthWithLessThan31Days LocalTime {..} =
  let (year, month, day) = toGregorian localDay
      isLastDay = gregorianMonthLength year month == day
   in day < 31 && isLastDay

moveToEndOfMonth :: LocalTime -> LocalTime
moveToEndOfMonth LocalTime {..} =
  let (year, month, _) = toGregorian localDay
      monthLength = gregorianMonthLength year month
   in LocalTime {localDay = fromGregorian year month monthLength, localTimeOfDay = localTimeOfDay}
