module Data.UUID.Extras
    ( isValidVersion
    , mockUUIDs
    , mockUUIDToSequenceId
    , sequenceIdToMockUUID
    ) where

import           Data.Bits            (shiftL, (.&.))
import qualified Data.ByteString.Lazy as BL
import           Data.UUID            (UUID)
import qualified Data.UUID            as UUID
import           Data.Word            (Word32)

-- This is taken directly from the test suite of
-- 'uuid:Data.UUID'. Strange that they don't include it in the core
-- library.
isValidVersion :: Int -> UUID -> Bool
isValidVersion v u = lenOK && variantOK && versionOK
  where
    bs = UUID.toByteString u
    lenOK = BL.length bs == 16
    variantOK = (BL.index bs 8) .&. 0xc0 == 0x80
    versionOK = (BL.index bs 6) .&. 0xf0 == fromIntegral (v `shiftL` 4)

-- | Given a UUID from 'mockUUIDs`, returns a simple sequence
-- number. Returns 'Nothing' if your UUID doesn't seem to come from
-- that sequence. As the name suggests, you should really only be
-- using this for mocking/testing.
mockUUIDToSequenceId :: UUID -> Maybe Word32
mockUUIDToSequenceId uuid =
    case UUID.toWords uuid of
        (0, 0x4000, 0x80000000, x) -> Just x
        _                          -> Nothing

-- | Create a UUID that can be used in testing, from a simple 'Word32'.
-- Reminder: Use 'fromIntegral i' to call it with an 'Int'.
sequenceIdToMockUUID :: Word32 -> UUID
sequenceIdToMockUUID = UUID.fromWords 0 0x4000 0x80000000

-- | A pure list of UUIDs that can be used in testing. This is
-- _almost_ a sequence counting up from zero, but we ensure that the
-- version and variant numbers are correctly set so the resulting UUIDs
-- validate.
mockUUIDs :: [UUID]
mockUUIDs = sequenceIdToMockUUID <$> enumFromTo minBound maxBound
