{-# LANGUAGE RecordWildCards #-}
module Language.Marlowe.ACTUS.HP.Utility.Annuity where

import Data.Maybe
import Data.Time
import qualified Data.List as List

import Language.Marlowe.ACTUS.HP.ContractTerms
import Language.Marlowe.ACTUS.HP.Utility.YearFraction

calculateAnnuity ::
  DCC -> [Day] -> Day -> Day -> Day -> Double -> Double -> Double -> Double
calculateAnnuity dcc prSchedule maturityDate s t n a r =
  let scheduleTimes = List.filter (> s) prSchedule
      m = (List.length scheduleTimes) - 1
  in
    (n + a) *
    (
      (calculateAnnuityProductFragment dcc maturityDate 0 m r scheduleTimes) /
      (1 + (calculateAnnuitySumFragment dcc maturityDate 0 m r scheduleTimes))
    )

calculateAnnuityProductFragment ::
  DCC -> Day -> Int -> Int -> Double -> [Day] -> Double
calculateAnnuityProductFragment dayCountConvention maturityDate i m r scheduleTimes
  | i == m =
    1
  | otherwise =
    let yearFraction' =
          yearFraction dayCountConvention (scheduleTimes !! i)
            (scheduleTimes !! (i + 1)) maturityDate
    in
      (1 + r * yearFraction') * (calculateAnnuityProductFragment dayCountConvention maturityDate (i + 1) m r scheduleTimes)

calculateAnnuitySumFragment ::
  DCC -> Day -> Int -> Int -> Double -> [Day] -> Double
calculateAnnuitySumFragment dcc maturityDate i m r scheduleTimes
  | i == m =
    0
  | otherwise =
    (calculateAnnuityProductFragment dcc maturityDate i m r scheduleTimes) +
      (calculateAnnuitySumFragment dcc maturityDate (i + 1) m r scheduleTimes)
