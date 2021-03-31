module Duration where

import Prelude
import Data.Int (floor, round, toNumber)
import Data.Time.Duration (Seconds(..))

humanizeDuration :: Seconds -> String
humanizeDuration (Seconds seconds)
  | seconds <= 0.0 = "timed out"
  | seconds < 60.0 = show (floor seconds) <> "sec left"
  | seconds < (60.0 * 60.0) =
    let
      min = floor (seconds / 60.0)

      sec = floor $ seconds - (toNumber min * 60.0)
    in
      show min <> "min " <> show sec <> "s left"
  | seconds < (60.0 * 60.0 * 24.0) =
    let
      hours = floor (seconds / 60.0 / 60.0)

      min = round $ (seconds - (toNumber hours * 60.0 * 60.0)) / 60.0
    in
      show hours <> "hr " <> show min <> "m left"
  | otherwise =
    let
      days = floor (seconds / 60.0 / 60.0 / 24.0)
    in
      if (days == 1) then
        "1 day left"
      else
        show days <> "days left"
