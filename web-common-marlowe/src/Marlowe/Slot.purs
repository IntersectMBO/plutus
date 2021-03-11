-- This module helps you work with slots and DateTimes. We only care about the current slot algorithm
-- that was introduced when Shelley was launched in mid 2020. Since the launch, each slot number
-- corresponds to a second.
module Marlowe.Slot (slotToDateTime, dateTimeToSlot, currentSlot) where

import Prelude
import Data.BigInteger (fromInt)
import Data.BigInteger as BigInteger
import Data.DateTime (DateTime, adjust, diff)
import Data.DateTime.Instant (instant, toDateTime)
import Data.Int (round)
import Data.Maybe (Maybe, fromJust)
import Data.Newtype (unwrap)
import Data.Time.Duration (Milliseconds(..), Seconds(..))
import Effect (Effect)
import Effect.Now (now)
import Marlowe.Semantics (Slot(..))
import Partial.Unsafe (unsafePartial)

-- This was the slot number when shelley was released
-- FIXME: check with Alex the exact number
shelleyInitialSlot :: Slot
shelleyInitialSlot = Slot $ fromInt 4492800

-- This was the exact DateTime where shelley was released
-- FIXME: check with Alex if the date and time are correct
shelleyLaunchDate :: DateTime
shelleyLaunchDate =
  let
    -- Wednesday, July 29, 2020 21:44:51 UTC expressed as unix epoch
    epoch = Milliseconds 1596059091000.0
  in
    unsafePartial $ fromJust $ toDateTime <$> instant epoch

slotToDateTime :: Slot -> Maybe DateTime
slotToDateTime slot =
  let
    secondsDiff :: Seconds
    secondsDiff = Seconds $ BigInteger.toNumber $ unwrap $ slot - shelleyInitialSlot
  in
    adjust secondsDiff shelleyLaunchDate

dateTimeToSlot :: DateTime -> Slot
dateTimeToSlot datetime =
  let
    secondsDiff :: Seconds
    secondsDiff = diff datetime shelleyLaunchDate
  in
    shelleyInitialSlot + (Slot $ BigInteger.fromInt $ round $ unwrap secondsDiff)

currentSlot :: Effect Slot
currentSlot = dateTimeToSlot <<< toDateTime <$> now
