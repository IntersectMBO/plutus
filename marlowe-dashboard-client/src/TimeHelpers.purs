module TimeHelpers where

import Prelude
import Data.DateTime (DateTime)
import Data.Formatter.DateTime as Formatter
import Data.Int (floor, round, toNumber)
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Seconds(..))
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Marlowe.Semantics (Slot, SlotInterval(..))
import Marlowe.Slot (slotToDateTime)

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

formatDate :: DateTime -> String
formatDate =
  Formatter.format
    $ List.fromFoldable
        [ Formatter.DayOfMonth
        , Formatter.Placeholder " "
        , Formatter.MonthShort
        , Formatter.Placeholder " "
        , Formatter.YearFull
        ]

formatTime :: DateTime -> String
formatTime =
  Formatter.format
    $ List.fromFoldable
        [ Formatter.Hours24
        , Formatter.Placeholder ":"
        , Formatter.MinutesTwoDigits
        ]

formatSlot :: Slot -> Maybe (Tuple String String)
formatSlot slot = (\slotDT -> formatDate slotDT /\ formatTime slotDT) <$> slotToDateTime slot

-- FIXME: Probably need to adjust with timezone
humanizeInterval :: SlotInterval -> String
humanizeInterval (SlotInterval from to) = humanize (formatSlot from) (formatSlot to)
  where
  humanize Nothing _ = "invalid interval"

  humanize _ Nothing = "invalid interval"

  humanize (Just (fromDate /\ fromTime)) (Just (toDate /\ toTime))
    | fromDate == toDate && fromTime == toTime = "on " <> fromDate <> " at " <> fromTime
    | fromDate == toDate = "on " <> fromDate <> " between " <> fromTime <> " and " <> toTime
    | otherwise = "between " <> fromDate <> " " <> fromTime <> " and " <> toDate <> " " <> toTime
