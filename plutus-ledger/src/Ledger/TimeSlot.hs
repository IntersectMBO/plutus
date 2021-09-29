{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}

{-# OPTIONS_GHC -Wno-orphans        #-}

module Ledger.TimeSlot(
  SlotConfig(..)
, SlotConversionError(..)
, slotRangeToPOSIXTimeRange
, slotToPOSIXTimeRange
, slotToBeginPOSIXTime
, slotToEndPOSIXTime
, posixTimeRangeToContainedSlotRange
, posixTimeToEnclosingSlot
, currentSlot
) where

import           Codec.Serialise           (Serialise)
import           Control.DeepSeq           (NFData)
import           Data.Aeson                (FromJSON, ToJSON)
import           Data.Default              (Default (def))
import           Data.Text.Prettyprint.Doc (Pretty (pretty), (<+>))
import qualified Data.Time.Clock           as Time
import qualified Data.Time.Clock.POSIX     as Time
import           GHC.Generics              (Generic)
import           Plutus.V1.Ledger.Interval (Extended (..), Interval (Interval), LowerBound (..), UpperBound (..),
                                            interval, member)
import           Plutus.V1.Ledger.Slot     (Slot (Slot), SlotRange)
import           Plutus.V1.Ledger.Time     (POSIXTime (POSIXTime, getPOSIXTime), POSIXTimeRange)
import           PlutusTx.Lift             (makeLift)
import           PlutusTx.Prelude          hiding (Eq, (<$>))
import           Prelude                   (Eq, IO, Show, (<$>))
import qualified Prelude                   as Haskell

-- | Datatype to configure the length (ms) of one slot and the beginning of the
-- first slot.
data SlotConfig =
    SlotConfig
        { scSlotLength   :: Integer -- ^ Length (number of milliseconds) of one slot
        , scSlotZeroTime :: POSIXTime -- ^ Beginning of slot 0 (in milliseconds)
        }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON, Serialise, NFData)

makeLift ''SlotConfig

instance Default SlotConfig where
    {-# INLINABLE def #-}
    def = SlotConfig{ scSlotLength = 1000, scSlotZeroTime = POSIXTime beginningOfTime }

instance Pretty SlotConfig where
    pretty SlotConfig {scSlotLength, scSlotZeroTime} =
            "Slot 0 starts at"
        <+> pretty scSlotZeroTime
        <+> "and one slot has length of"
        <+> pretty scSlotLength
        <+> "ms"

data SlotConversionError =
    SlotOutOfRange
        { requestedSlot :: Slot
        , horizon       :: (Slot, POSIXTime)
        }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty SlotConversionError where
    pretty SlotOutOfRange { requestedSlot, horizon } =
            "Slot out of range:"
        <+> pretty requestedSlot
        <+> "Horizon:"
        <+> pretty horizon

{-# INLINABLE beginningOfTime #-}
-- | 'beginningOfTime' corresponds to the Shelley launch date
-- (2020-07-29T21:44:51Z) which is 1596059091000 in POSIX time
-- (number of milliseconds since 1970-01-01T00:00:00Z).
beginningOfTime :: Integer
beginningOfTime = 1596059091000

{-# INLINABLE slotRangeToPOSIXTimeRange #-}
-- | Convert a 'SlotRange' to a 'POSIXTimeRange' given a 'SlotConfig'. The
-- resulting 'POSIXTimeRange' refers to the starting time of the lower bound of
-- the 'SlotRange' and the ending time of the upper bound of the 'SlotRange'.
slotRangeToPOSIXTimeRange :: SlotConfig -> SlotRange -> POSIXTimeRange
slotRangeToPOSIXTimeRange sc (Interval (LowerBound start startIncl) (UpperBound end endIncl)) =
  let lbound = fmap (if startIncl then slotToBeginPOSIXTime sc else slotToEndPOSIXTime sc) start
      ubound = fmap (if endIncl   then slotToEndPOSIXTime sc   else slotToBeginPOSIXTime sc) end
   in Interval (LowerBound lbound startIncl) (UpperBound ubound endIncl)

{-# INLINABLE slotToPOSIXTimeRange #-}
-- | Convert a 'Slot' to a 'POSIXTimeRange' given a 'SlotConfig'. Each 'Slot'
-- can be represented by an interval of time.
slotToPOSIXTimeRange :: SlotConfig -> Slot -> POSIXTimeRange
slotToPOSIXTimeRange sc slot =
  interval (slotToBeginPOSIXTime sc slot) (slotToEndPOSIXTime sc slot)

{-# INLINABLE slotToBeginPOSIXTime #-}
-- | Get the starting 'POSIXTime' of a 'Slot' given a 'SlotConfig'.
slotToBeginPOSIXTime :: SlotConfig -> Slot -> POSIXTime
slotToBeginPOSIXTime SlotConfig{scSlotLength, scSlotZeroTime} (Slot n) =
  let msAfterBegin = n * scSlotLength
   in POSIXTime $ getPOSIXTime scSlotZeroTime + msAfterBegin

{-# INLINABLE slotToEndPOSIXTime #-}
-- | Get the ending 'POSIXTime' of a 'Slot' given a 'SlotConfig'.
slotToEndPOSIXTime :: SlotConfig -> Slot -> POSIXTime
slotToEndPOSIXTime sc@SlotConfig{scSlotLength} slot =
  slotToBeginPOSIXTime sc slot + POSIXTime (scSlotLength - 1)

{-# INLINABLE posixTimeRangeToContainedSlotRange #-}
-- | Convert a 'POSIXTimeRange' to 'SlotRange' given a 'SlotConfig'. This gives
-- the biggest slot range that is entirely contained by the given time range.
posixTimeRangeToContainedSlotRange :: SlotConfig -> POSIXTimeRange -> SlotRange
posixTimeRangeToContainedSlotRange sc ptr = case fmap (posixTimeToEnclosingSlot sc) ptr of
  Interval (LowerBound start startIncl) (UpperBound end endIncl) ->
    Interval
      (LowerBound start (case start of Finite s -> slotToBeginPOSIXTime sc s `member` ptr; _ -> startIncl))
      (UpperBound end (case end of Finite e -> slotToEndPOSIXTime sc e `member` ptr; _ -> endIncl))

{-# INLINABLE posixTimeToEnclosingSlot #-}
-- | Convert a 'POSIXTime' to 'Slot' given a 'SlotConfig'.
posixTimeToEnclosingSlot :: SlotConfig -> POSIXTime -> Slot
posixTimeToEnclosingSlot SlotConfig{scSlotLength, scSlotZeroTime} (POSIXTime t) =
  let timePassed = t - getPOSIXTime scSlotZeroTime
      slotsPassed = divide timePassed scSlotLength
  in Slot slotsPassed

-- | Get the current slot number
currentSlot :: SlotConfig -> IO Slot
currentSlot sc = timeToSlot <$> Time.getPOSIXTime
    where
      timeToSlot = posixTimeToEnclosingSlot sc
                 . POSIXTime
                 . (* 1000) -- Convert to ms
                 . Haskell.floor
                 . Time.nominalDiffTimeToSeconds

