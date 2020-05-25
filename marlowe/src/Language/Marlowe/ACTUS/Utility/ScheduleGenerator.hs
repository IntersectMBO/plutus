{-# LANGUAGE RecordWildCards #-}
module Language.Marlowe.ACTUS.Utility.ScheduleGenerator(
  generateRecurrentScheduleWithCorrections
  , plusCycle
  , sup
  , inf
  , remove
) where

import Data.Time.Calendar
import qualified Data.List as L

import Language.Marlowe.ACTUS.ContractTerms
import Language.Marlowe.ACTUS.Schedule
import Language.Marlowe.ACTUS.Utility.DateShift

sup :: [ShiftedDay] -> Day -> ShiftedDay
sup set threshold = minimum (filter (\t -> (calculationDay t) >= threshold) set)

inf :: [ShiftedDay] -> Day -> ShiftedDay
inf set threshold = maximum (filter (\t -> (calculationDay t) <= threshold) set)

remove :: ShiftedDay -> [ShiftedDay] -> [ShiftedDay]
remove d set = (filter (\t -> (calculationDay t) /= (calculationDay d)) set)

type AnchorDay = Day
type EndDay = Day

stubCorrection :: Stub -> EndDay -> ShiftedSchedule -> ShiftedSchedule
stubCorrection stub endDay schedule =
  if (paymentDay $ L.last schedule) == endDay && stub == ShortStub then schedule else L.init schedule

endDateCorrection :: Bool -> EndDay -> Schedule -> Schedule
endDateCorrection includeEndDay endDay schedule 
  | includeEndDay && not (L.elem endDay schedule) = schedule ++ [endDay]
  | (not includeEndDay) && (L.elem endDay schedule) = L.init schedule
  | otherwise = schedule

generateRecurrentSchedule :: Cycle -> AnchorDay -> EndDay -> Schedule
generateRecurrentSchedule Cycle{..} anchorDate endDate = 
  let 
    go :: Day -> Integer -> [Day] -> [Day]
    go current k acc = if current > endDate then acc
                                            else (let current' = shiftDate anchorDate (k * n) p
                                                 in go current' (k + 1) (acc ++ [current]))
  in go anchorDate 0 []                                                
                                              

generateRecurrentScheduleWithCorrections :: AnchorDay -> Cycle -> EndDay -> ScheduleConfig -> ShiftedSchedule
generateRecurrentScheduleWithCorrections anchorDate cycle endDate ScheduleConfig{..} = 
  let schedule = generateRecurrentSchedule cycle anchorDate endDate
      schedule' = endDateCorrection includeEndDay endDate schedule
      schedule'' = L.map (applyEOMC anchorDate cycle eomc) schedule'
      schedule''' = L.map (applyBDC bdc calendar) schedule''
      schedule'''' = stubCorrection (stub cycle) endDate schedule'''
  in  schedule''''

plusCycle :: Day -> Cycle -> Day 
plusCycle date cycle = shiftDate date (n cycle) (p cycle)

shiftDate :: Day -> Integer -> Period -> Day
shiftDate date n p =
  case p  of
    P_D -> addDays n date
    P_W -> addDays (n * 7) date
    P_M -> addGregorianMonthsClip n date
    P_Q -> addGregorianMonthsClip (n * 3) date
    P_H -> addGregorianMonthsClip (n * 6) date
    P_Y -> addGregorianYearsClip n date


{- End of Month Convention -}
applyEOMC :: Day -> Cycle -> EOMC -> Day -> Day
applyEOMC s Cycle{n = n, p = p} endOfMonthConvention date
  | ((isLastDayOfMonthWithLessThan31Days s) &&
      p /= P_D && p /= P_W &&
      endOfMonthConvention == EOMC_EOM
    ) =
    moveToEndOfMonth date
  | otherwise =
    date

isLastDayOfMonthWithLessThan31Days :: Day -> Bool
isLastDayOfMonthWithLessThan31Days date =
  let (day, month, year) = toGregorian date
  in
    day < 31 && (gregorianMonthLength (toInteger year) month) == (fromInteger day) 

moveToEndOfMonth :: Day -> Day
moveToEndOfMonth date =
  let (_, month, year) = toGregorian date
      monthLength = gregorianMonthLength (toInteger year) month
  in
    fromGregorian (toInteger year) month monthLength
