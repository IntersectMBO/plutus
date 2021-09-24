{-# LANGUAGE RecordWildCards #-}

{- This module provides compatibility to Marlowe DSL -}

module Language.Marlowe.ACTUS.MarloweCompat where

import           Data.String                (IsString (fromString))
import           Data.Time                  (Day, LocalTime (..), UTCTime (UTCTime), timeOfDayToTime)
import           Data.Time.Clock.System     (SystemTime (MkSystemTime), utcToSystemTime)
import           Language.Marlowe           (Contract (Let), Observation, Value (Constant, UseValue), ValueId (ValueId))
import           Language.Marlowe.ACTUS.Ops (marloweFixedPoint)

useval :: String -> Integer -> Value Observation
useval name t = UseValue $ ValueId $ fromString $ name ++ "_" ++ show t

letval :: String -> Integer -> Value Observation -> Contract -> Contract
letval name t = Let $ ValueId $ fromString $ name ++ "_" ++ show t

toMarloweFixedPoint :: Double -> Integer
toMarloweFixedPoint = round <$> (fromIntegral marloweFixedPoint *)

constnt :: Double -> Value Observation
constnt = Constant . toMarloweFixedPoint

enum :: a -> a
enum = id

cardanoEpochStart :: Integer
cardanoEpochStart = 100

dayToSlotNumber :: Day -> Integer
dayToSlotNumber d =
  let (MkSystemTime secs _) = utcToSystemTime (UTCTime d 0)
   in fromIntegral secs - cardanoEpochStart

timeToSlotNumber :: LocalTime -> Integer
timeToSlotNumber LocalTime {..} =
  let (MkSystemTime secs _) = utcToSystemTime (UTCTime localDay (timeOfDayToTime localTimeOfDay))
   in fromIntegral secs - cardanoEpochStart

marloweDate :: Day -> Value Observation
marloweDate = Constant . fromInteger . dayToSlotNumber

marloweTime :: LocalTime -> Value Observation
marloweTime = Constant . fromInteger . timeToSlotNumber
