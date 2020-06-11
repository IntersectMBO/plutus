{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Language.Marlowe.ACTUS.Utility.ScheduleGenerator
  ( generateRecurrentScheduleWithCorrections
  , plusCycle
  , sup
  , inf
  , remove
  )
where

import Data.Time.Calendar
    ( Day,
      addGregorianMonthsClip,
      addGregorianYearsClip,
      fromGregorian,
      gregorianMonthLength,
      toGregorian,
      addDays )
import qualified Data.List as L ( elem, notElem, init, last )
import Language.Marlowe.ACTUS.ContractTerms
    ( ScheduleConfig(..),
      Cycle(..),
      Stub(ShortStub),
      Period(..),
      EOMC(EOMC_EOM) )
import Language.Marlowe.ACTUS.Schedule
    ( ShiftedSchedule,
      ShiftedDay(calculationDay, paymentDay),
      Schedule )
import Language.Marlowe.ACTUS.Utility.DateShift ( applyBDC )


sup :: [ShiftedDay] -> Day -> ShiftedDay
sup set threshold =
  minimum [t | t <- set, calculationDay t >= threshold]

inf :: [ShiftedDay] -> Day -> ShiftedDay
inf set threshold =
  maximum [t | t <- set, calculationDay t <= threshold]

remove :: ShiftedDay -> [ShiftedDay] -> [ShiftedDay]
remove d = filter (\t -> calculationDay t /= calculationDay d)

type AnchorDay = Day
type EndDay = Day

stubCorrection :: Stub -> EndDay -> ShiftedSchedule -> ShiftedSchedule
stubCorrection stub endDay schedule =
  if (paymentDay $ L.last schedule) == endDay && stub == ShortStub
    then schedule
    else L.init schedule

endDateCorrection :: Bool -> EndDay -> Schedule -> Schedule
endDateCorrection includeEndDay endDay schedule
  | includeEndDay && L.notElem endDay schedule = schedule ++ [endDay]
  | not includeEndDay && L.elem endDay schedule = L.init schedule
  | otherwise = schedule

generateRecurrentSchedule :: Cycle -> AnchorDay -> EndDay -> Schedule
generateRecurrentSchedule Cycle {..} anchorDate endDate =
  let go :: Day -> Integer -> [Day] -> [Day]
      go current k acc = if current > endDate
        then acc
        else
          (let current' = shiftDate anchorDate (k * n) p
           in  go current' (k + 1) (acc ++ [current])
          )
  in  go anchorDate 0 []


generateRecurrentScheduleWithCorrections
  :: AnchorDay -> Cycle -> EndDay -> ScheduleConfig -> ShiftedSchedule
generateRecurrentScheduleWithCorrections anchorDate cycle endDate ScheduleConfig {..}
  = let schedule     = generateRecurrentSchedule cycle anchorDate endDate
        schedule'    = endDateCorrection includeEndDay endDate schedule
        schedule''    = applyEOMC anchorDate cycle eomc <$> schedule'
        schedule'''   = applyBDC bdc calendar <$> schedule''
        schedule''''   = stubCorrection (stub cycle) endDate schedule'''
    in  schedule''''

plusCycle :: Day -> Cycle -> Day
plusCycle date cycle = shiftDate date (n cycle) (p cycle)

shiftDate :: Day -> Integer -> Period -> Day
shiftDate date n p = case p of
  P_D -> addDays n date
  P_W -> addDays (n * 7) date
  P_M -> addGregorianMonthsClip n date
  P_Q -> addGregorianMonthsClip (n * 3) date
  P_H -> addGregorianMonthsClip (n * 6) date
  P_Y -> addGregorianYearsClip n date


{- End of Month Convention -}
applyEOMC :: Day -> Cycle -> EOMC -> Day -> Day
applyEOMC s Cycle {..} endOfMonthConvention date
  | isLastDayOfMonthWithLessThan31Days s
    && p /= P_D
    && p /= P_W
    && endOfMonthConvention == EOMC_EOM   
  = moveToEndOfMonth date
  | otherwise
  = date

isLastDayOfMonthWithLessThan31Days :: Day -> Bool
isLastDayOfMonthWithLessThan31Days date =
  let (day, month, year) = toGregorian date
      isLastDay = gregorianMonthLength (toInteger year) month == fromInteger day
  in  day <  31 && isLastDay

moveToEndOfMonth :: Day -> Day
moveToEndOfMonth date =
  let (_, month, year) = toGregorian date
      monthLength      = gregorianMonthLength (toInteger year) month
  in  fromGregorian (toInteger year) month monthLength
