{-# LANGUAGE RecordWildCards #-}
module Language.Marlowe.ACTUS.HP.Utility.ScheduleGenerator(
  generateRecurrentScheduleWithCorrections
  , plusCycle
) where

import Data.Char
import Data.Time.Calendar
import qualified Data.List as L

import Language.Marlowe.ACTUS.HP.ContractTerms
import Language.Marlowe.ACTUS.HP.Schedule
import Language.Marlowe.ACTUS.HP.Utility.DateShift

mapPeriod :: Char -> Period
mapPeriod periodChar = case periodChar of
  'D' -> P_D
  'W' -> P_W
  'M' -> P_M
  'Q' -> P_Q
  'H' -> P_H
  'Y' -> P_Y

mapStub :: Char -> Stub
mapStub stubChar = case stubChar of
  '-' -> ShortStub
  '+' -> LongStub

createCycle :: [Char] -> Cycle
createCycle [n, periodChar, stubChar] = Cycle
  { n = toInteger (digitToInt n)
  , p = mapPeriod periodChar
  , stub = mapStub stubChar
  }

type AnchorDay = Day
type EndDay = Day

stubCorrection :: Stub -> EndDay -> ShiftedSchedule -> ShiftedSchedule
stubCorrection stub endDay schedule =
  if (paymentDay $ L.last schedule) == endDay && stub == ShortStub then schedule else L.init schedule

endDateCorrection :: Bool -> EndDay -> Schedule -> Schedule
endDateCorrection includeEndDay endDay schedule 
  | includeEndDay && not (L.elem endDay schedule) = schedule ++ [endDay]
  | (not includeEndDay) && (L.elem endDay schedule) = L.init schedule

generateRecurrentSchedule :: Cycle -> AnchorDay -> EndDay -> Schedule
generateRecurrentSchedule cycle@Cycle{..} anchorDate endDate = 
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
applyEOMC s cycle@Cycle{n = n, p = p} endOfMonthConvention date
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
  let (day, month, year) = toGregorian date
      monthLength = gregorianMonthLength (toInteger year) month
  in
    fromGregorian (toInteger year) month monthLength
