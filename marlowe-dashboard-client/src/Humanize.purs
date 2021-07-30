module Humanize
  ( adjustTimeZone
  , humanizeDuration
  , formatDate
  , formatDate'
  , formatTime
  , formatTime'
  , getTimezoneOffset
  , humanizeInterval
  , humanizeValue
  , contractIcon
  ) where

import Prelude
import Data.BigInteger (BigInteger, toNumber)
import Data.DateTime (DateTime, adjust)
import Data.Formatter.DateTime (FormatterCommand(..), format) as DateTime
import Data.Formatter.Number (Formatter(..), format) as Number
import Data.Int (floor, round)
import Data.Int (toNumber) as Int
import Data.List as List
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap, wrap)
import Data.Time.Duration (Minutes, Seconds(..))
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Now as Now
import Halogen.HTML (HTML, img)
import Halogen.HTML.Properties (src)
import Images (cfdIcon, loanIcon, purchaseIcon)
import Marlowe.Extended (ContractType(..))
import Marlowe.Semantics (Slot, SlotInterval(..), Token(..))
import Marlowe.Slot (slotToDateTime)

humanizeDuration :: Seconds -> String
humanizeDuration (Seconds seconds)
  | seconds <= 0.0 = "Timed out"
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

humanizeInterval :: Minutes -> SlotInterval -> String
humanizeInterval tzOffset (SlotInterval from to) = humanize (formatSlot tzOffset from) (formatSlot tzOffset to)
  where
  humanize Nothing _ = "invalid interval"

  humanize _ Nothing = "invalid interval"

  humanize (Just (fromDate /\ fromTime)) (Just (toDate /\ toTime))
    | fromDate == toDate && fromTime == toTime = "on " <> fromDate <> " at " <> fromTime
    | fromDate == toDate = "on " <> fromDate <> " between " <> fromTime <> " and " <> toTime
    | otherwise = "between " <> fromDate <> " " <> fromTime <> " and " <> toDate <> " " <> toTime

formatSlot :: Minutes -> Slot -> Maybe (Tuple String String)
formatSlot tzOffset slot =
  slotToDateTime slot
    <#> \slotDT ->
        let
          adjustedDt = adjustTimeZone tzOffset slotDT
        in
          formatDate' adjustedDt /\ formatTime' adjustedDt

-- This is a small wrapper around Now.getTimezoneOffset to be used in conjunction with
-- adjustTimeZone. We need to negate the value in order to substract when we do the
-- adjust, and Minutes does not have a Ring instance, so we need to unwrap and re-wrap
getTimezoneOffset :: Effect Minutes
getTimezoneOffset = wrap <<< negate <<< unwrap <$> Now.getTimezoneOffset

-- Adjusts a DateTime via an offset (that can be obtained using getTimezoneOffset)
-- The `adjust` function can overflow, if that happens (it shouldn't) we resolve to
-- the original value
adjustTimeZone :: Minutes -> DateTime -> DateTime
adjustTimeZone tzOffset dt = fromMaybe dt (adjust tzOffset dt)

formatDate :: Minutes -> DateTime -> String
formatDate tzOffset dt = formatDate' $ adjustTimeZone tzOffset dt

formatDate' :: DateTime -> String
formatDate' =
  DateTime.format
    $ List.fromFoldable
        [ DateTime.DayOfMonth
        , DateTime.Placeholder " "
        , DateTime.MonthShort
        , DateTime.Placeholder " "
        , DateTime.YearFull
        ]

formatTime :: Minutes -> DateTime -> String
formatTime tzOffset dt = formatTime' $ adjustTimeZone tzOffset dt

formatTime' :: DateTime -> String
formatTime' =
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

contractIcon :: forall p a. ContractType -> HTML p a
contractIcon contractType =
  img
    [ src case contractType of
        Escrow -> purchaseIcon
        ZeroCouponBond -> loanIcon
        _ -> cfdIcon
    ]
