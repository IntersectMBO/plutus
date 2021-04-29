-- This module helps you work with slots and DateTimes. We only care about the current slot algorithm
-- that was introduced when Shelley was launched in mid 2020. Since the launch, each slot number
-- corresponds to a second.
module Marlowe.Slot
  ( shelleyInitialSlot
  , slotToDateTime
  , dateTimeToSlot
  , dateTimeStringToSlot
  , currentSlot
  , secondsDiff
  ) where

import Prelude
import Data.BigInteger (fromInt)
import Data.BigInteger as BigInteger
import Data.DateTime (DateTime, adjust, diff)
import Data.DateTime.Instant (instant, toDateTime)
import Data.Either (Either(..))
import Data.Formatter.DateTime (Formatter, FormatterCommand(..), unformat) as FDT
import Data.Int (round)
import Data.List (fromFoldable)
import Data.Maybe (Maybe(..), fromJust)
import Data.Newtype (unwrap)
import Data.Time.Duration (Milliseconds(..), Seconds(..))
import Effect (Effect)
import Effect.Now (now)
import Marlowe.Semantics (Slot(..))
import Partial.Unsafe (unsafePartial)

-- TODO: When we are integrated with the real Cardano node, we will need to
-- know the datetime of one slot so that we can convert slots to and from
-- datetimes. Any slot will do, but to avoid arbitrariness it would be nice
-- to know the exact datetime of the Shelley launch, and the slot number at
-- that moment. In the meantime, these are our best guesses based on some
-- quick Googling.  :)
shelleyInitialSlot :: Slot
shelleyInitialSlot = Slot $ fromInt 4492800

-- Note [Datetime to slot]: The `plutus-pab.yaml` config file can specify
-- the datetime of slot zero. To synchronise with the frontend, this should
-- be set to `shelleyLaunchDate - (shelleyInitialSlot * 1000)` (because there
-- is 1 slot per second). On the current estimates this comes to 1591566291000,
-- which is 2020-06-07 21:44:51 UTC.
shelleyLaunchDate :: DateTime
shelleyLaunchDate =
  let
    -- 2020-07-29 21:44:51 UTC expressed as unix epoch
    epoch = Milliseconds 1596059091000.0
  in
    unsafePartial $ fromJust $ toDateTime <$> instant epoch

secondsDiff :: Slot -> Slot -> Seconds
secondsDiff a b = Seconds $ BigInteger.toNumber $ unwrap $ a - b

slotToDateTime :: Slot -> Maybe DateTime
slotToDateTime slot =
  let
    secondsDiff' = secondsDiff slot shelleyInitialSlot
  in
    adjust secondsDiff' shelleyLaunchDate

dateTimeToSlot :: DateTime -> Slot
dateTimeToSlot datetime =
  let
    secondsDiff' :: Seconds
    secondsDiff' = diff datetime shelleyLaunchDate
  in
    shelleyInitialSlot + (Slot $ BigInteger.fromInt $ round $ unwrap secondsDiff')

dateTimeStringToSlot :: String -> Maybe Slot
dateTimeStringToSlot dateTimeString =
  let
    -- this is the format dateTimeStrings appear in an input[type="datetime-local"].value
    dateTimeFormat :: FDT.Formatter
    dateTimeFormat =
      fromFoldable
        [ FDT.YearAbsolute
        , FDT.Placeholder "-"
        , FDT.MonthTwoDigits
        , FDT.Placeholder "-"
        , FDT.DayOfMonthTwoDigits
        , FDT.Placeholder "T"
        , FDT.Hours24
        , FDT.Placeholder ":"
        , FDT.MinutesTwoDigits
        ]
  in
    case FDT.unformat dateTimeFormat dateTimeString of
      Right dateTime -> Just $ dateTimeToSlot dateTime
      Left _ -> Nothing

currentSlot :: Effect Slot
currentSlot = dateTimeToSlot <<< toDateTime <$> now
