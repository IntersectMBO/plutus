{-# LANGUAGE NoImplicitPrelude #-}

-- This GHC option prevents the error:
-- "GHC Core to PLC plugin: E042:Error: Unsupported feature: Kind: *"
-- Because Plutus can't handle unboxed tuples which come from worker/wrapper
{-# OPTIONS_GHC -fno-worker-wrapper #-}

module Ledger.TimeSlot(
  slotRangeToPOSIXTimeRange
, slotToPOSIXTime
, posixTimeRangeToSlotRange
, posixTimeToSlot
) where

import           Plutus.V1.Ledger.Slot (Slot (Slot), SlotRange)
import           Plutus.V1.Ledger.Time (POSIXTime (POSIXTime), POSIXTimeRange)
import           PlutusTx.Prelude

{-# INLINABLE shelleyLaunchDate #-}
-- | 'shelleyLaunchDatePOSIXTime' corresponds to the time 2020-07-29T21:44:51Z
-- which is 1596059091 in POSIX time (number of seconds since
-- 1970-01-01T00:00:00Z).
shelleyLaunchDate :: Integer
shelleyLaunchDate = 1596059091

{-# INLINABLE slotRangeToPOSIXTimeRange #-}
-- | Convert a 'SlotRange' to 'POSIXTimeRange'
slotRangeToPOSIXTimeRange :: SlotRange -> POSIXTimeRange
slotRangeToPOSIXTimeRange sr = slotToPOSIXTime <$> sr

{-# INLINABLE slotToPOSIXTime #-}
-- | Convert a 'Slot to 'POSIXTime
slotToPOSIXTime :: Slot -> POSIXTime
slotToPOSIXTime (Slot n) = POSIXTime (n + shelleyLaunchDate)

{-# INLINABLE posixTimeRangeToSlotRange #-}
-- | Convert a 'POSIXTimeRange' to 'SlotRange'
posixTimeRangeToSlotRange :: POSIXTimeRange -> SlotRange
posixTimeRangeToSlotRange ptr = posixTimeToSlot <$> ptr

{-# INLINABLE posixTimeToSlot #-}
-- | Convert a 'POSIXTime' to 'Slot'
posixTimeToSlot :: POSIXTime -> Slot
posixTimeToSlot (POSIXTime t) = Slot (t - shelleyLaunchDate)

