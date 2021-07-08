module Humanize
  ( humanizeDuration
  , formatDate
  , formatTime
  , humanizeInterval
  , humanizeValue
  ) where

import Prelude
import Data.BigInteger (BigInteger, toNumber)
import Data.DateTime (DateTime)
import Data.Formatter.DateTime (FormatterCommand(..), format) as DateTime
import Data.Formatter.Number (Formatter(..), format) as Number
import Data.Int (floor, round)
import Data.Int (toNumber) as Int
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Seconds(..))
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Marlowe.Semantics (Slot, SlotInterval(..), Token(..))
import Marlowe.Slot (slotToDateTime)

humanizeDuration :: Seconds -> String
humanizeDuration (Seconds seconds)
  | seconds <= 0.0 = "timed out"
  | seconds <= 60.0 = show (floor seconds) <> "sec left"
  | seconds <= (60.0 * 60.0) =
    let
      min = floor (seconds / 60.0)

      sec = floor $ seconds - (Int.toNumber min * 60.0)
    in
      show min <> "min " <> show sec <> "s left"
  | seconds < (60.0 * 60.0 * 24.0) =
    let
      hours = floor (seconds / 60.0 / 60.0)

      min = round $ (seconds - (Int.toNumber hours * 60.0 * 60.0)) / 60.0
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

formatSlot :: Slot -> Maybe (Tuple String String)
formatSlot slot = (\slotDT -> formatDate slotDT /\ formatTime slotDT) <$> slotToDateTime slot

formatDate :: DateTime -> String
formatDate =
  DateTime.format
    $ List.fromFoldable
        [ DateTime.DayOfMonth
        , DateTime.Placeholder " "
        , DateTime.MonthShort
        , DateTime.Placeholder " "
        , DateTime.YearFull
        ]

formatTime :: DateTime -> String
formatTime =
  DateTime.format
    $ List.fromFoldable
        [ DateTime.Hours24
        , DateTime.Placeholder ":"
        , DateTime.MinutesTwoDigits
        ]

humanizeValue :: Token -> BigInteger -> String
-- TODO: use a different currencyFormatter with no decimal places when they're all zero
humanizeValue (Token "" "") value = "₳ " <> Number.format (numberFormatter 6) (toAda value)

humanizeValue (Token "" "dollar") value = "$ " <> Number.format (numberFormatter 2) (toNumber value)

humanizeValue (Token _ name) value = Number.format (numberFormatter 0) (toNumber value) <> " " <> name

toAda :: BigInteger -> Number
toAda lovelace = (toNumber lovelace) / 1000000.0

numberFormatter :: Int -> Number.Formatter
numberFormatter decimals =
  Number.Formatter
    { sign: false
    , before: 0
    , comma: true
    , after: decimals
    , abbreviations: false
    }
