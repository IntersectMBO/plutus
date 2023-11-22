module PlutusCore.Builtin.Convert (
  IntegerToByteStringError(..),
  integerToByteString,
  byteStringToInteger
  ) where

import ByteString.StrictBuilder (Builder, builderBytes, builderLength, bytes, storable, word64BE,
                                 word8)
import Control.Monad (guard)
import Data.Bits (unsafeShiftL, unsafeShiftR, (.|.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Word (Word64)
import GHC.ByteOrder (ByteOrder (BigEndian, LittleEndian))

data IntegerToByteStringError =
  NegativeInput Integer |
  NotEnoughDigits Integer Int
  deriving stock (Eq, Show)

integerToByteString ::
  Int -> ByteOrder -> Integer -> Either IntegerToByteStringError ByteString
integerToByteString requestedLength requestedByteOrder i = case signum i of
  (-1) -> Left . NegativeInput $ i
  0 -> Right . BS.replicate (max 1 requestedLength) $ 0x00
  _ -> do
      let result = case (requestedByteOrder, requestedLength > 0) of
                      (LittleEndian, True)  -> goLELimit mempty i
                      (LittleEndian, False) -> pure $ goLENoLimit mempty i
                      (BigEndian, True)     -> goBELimit mempty i
                      (BigEndian, False)    -> pure $ goBENoLimit mempty i
      case result of
        Nothing -> Left . NotEnoughDigits i $ requestedLength
        Just b  -> pure . builderBytes $ b
  where
    goLELimit :: Builder -> Integer -> Maybe Builder
    goLELimit acc remaining
      | remaining == 0 = pure $ padLE acc
      | otherwise = do
          guard (builderLength acc < requestedLength)
          let newRemaining = remaining `unsafeShiftR` 64
          let digitGroup = fromInteger remaining
          case newRemaining of
            0 -> finishLELimit acc digitGroup
            _ -> goLELimit (acc <> storable digitGroup) newRemaining
    finishLELimit :: Builder -> Word64 -> Maybe Builder
    finishLELimit acc remaining
      | remaining == 0 = pure $ padLE acc
      | otherwise = do
          guard (builderLength acc < requestedLength)
          let newRemaining = remaining `unsafeShiftR` 8
          let digit = fromIntegral remaining
          finishLELimit (acc <> word8 digit) newRemaining
    goLENoLimit :: Builder -> Integer -> Builder
    goLENoLimit acc remaining
      | remaining == 0 = padLE acc
      | otherwise = let newRemaining = remaining `unsafeShiftR` 64
                        digitGroup = fromInteger remaining
          in case newRemaining of
              0 -> finishLENoLimit acc digitGroup
              _ -> goLENoLimit (acc <> storable digitGroup) newRemaining
    finishLENoLimit :: Builder -> Word64 -> Builder
    finishLENoLimit acc remaining
      | remaining == 0 = padLE acc
      | otherwise = let newRemaining = remaining `unsafeShiftR` 8
                        digit = fromIntegral remaining
                      in finishLENoLimit (acc <> word8 digit) newRemaining
    padLE :: Builder -> Builder
    padLE acc = acc <> bytes (BS.replicate (requestedLength - builderLength acc) 0x0)
    goBELimit :: Builder -> Integer -> Maybe Builder
    goBELimit acc remaining
      | remaining == 0 = pure $ padBE acc
      | otherwise = do
          guard (builderLength acc < requestedLength)
          let newRemaining = remaining `unsafeShiftR` 64
          let digitGroup = fromInteger remaining
          case newRemaining of
            0 -> finishBELimit acc digitGroup
            _ -> goBELimit (word64BE digitGroup <> acc) newRemaining
    finishBELimit :: Builder -> Word64 -> Maybe Builder
    finishBELimit acc remaining
      | remaining == 0 = pure $ padBE acc
      | otherwise = do
          guard (builderLength acc < requestedLength)
          let newRemaining = remaining `unsafeShiftR` 8
          let digit = fromIntegral remaining
          finishBELimit (word8 digit <> acc) newRemaining
    goBENoLimit :: Builder -> Integer -> Builder
    goBENoLimit acc remaining
      | remaining == 0 = padBE acc
      | otherwise = let newRemaining = remaining `unsafeShiftR` 64
                        digitGroup = fromInteger remaining
                      in case newRemaining of
                        0 -> finishBENoLimit acc digitGroup
                        _ -> goBENoLimit (word64BE digitGroup <> acc) newRemaining
    finishBENoLimit :: Builder -> Word64 -> Builder
    finishBENoLimit acc remaining
      | remaining == 0 = padBE acc
      | otherwise = let newRemaining = remaining `unsafeShiftR` 8
                        digit = fromIntegral remaining
                      in finishBENoLimit (word8 digit <> acc) newRemaining
    padBE :: Builder -> Builder
    padBE acc = bytes (BS.replicate (requestedLength - builderLength acc) 0x0) <> acc

byteStringToInteger :: ByteOrder -> ByteString -> Maybe Integer
byteStringToInteger statedByteOrder bs = do
  guard (not . BS.null $ bs)
  pure $ case statedByteOrder of
    LittleEndian -> case BS.findIndexEnd (/= 0x0) bs of
      Nothing  -> 0
      Just end -> goLE 0 end 0 0
    BigEndian -> case BS.findIndex (/= 0x0) bs of
      Nothing  -> 0
      Just end -> goBE 0 end 0 (BS.length bs - 1)
  where
    goLE :: Integer -> Int -> Int -> Int -> Integer
    goLE acc limit shift ix
      | ix <= (limit - 7) =
          let digitGroup = read64LE ix
              newShift = shift + 64
              newIx = ix + 8
           in if digitGroup == 0
                then goLE acc limit newShift newIx
                else
                  goLE (acc + fromIntegral digitGroup `unsafeShiftL` shift) limit newShift newIx
      | otherwise = finishLE acc limit shift ix
    finishLE :: Integer -> Int -> Int -> Int -> Integer
    finishLE acc limit shift ix
      | ix > limit = acc
      | otherwise =
          let digit = BS.index bs ix
              newShift = shift + 8
              newIx = ix + 1
           in if digit == 0
                then finishLE acc limit newShift newIx
                else finishLE (acc + fromIntegral digit `unsafeShiftL` shift) limit newShift newIx
    read64LE :: Int -> Word64
    read64LE startIx =
      fromIntegral (BS.index bs startIx)
        .|. (fromIntegral (BS.index bs (startIx + 1)) `unsafeShiftL` 8)
        .|. (fromIntegral (BS.index bs (startIx + 2)) `unsafeShiftL` 16)
        .|. (fromIntegral (BS.index bs (startIx + 3)) `unsafeShiftL` 24)
        .|. (fromIntegral (BS.index bs (startIx + 4)) `unsafeShiftL` 32)
        .|. (fromIntegral (BS.index bs (startIx + 5)) `unsafeShiftL` 40)
        .|. (fromIntegral (BS.index bs (startIx + 6)) `unsafeShiftL` 48)
        .|. (fromIntegral (BS.index bs (startIx + 7)) `unsafeShiftL` 56)
    goBE :: Integer -> Int -> Int -> Int -> Integer
    goBE acc limit shift ix
      | ix >= (limit + 7) =
          let digitGroup = read64BE ix
              newShift = shift + 64
              newIx = ix - 8
           in if digitGroup == 0
                then goBE acc limit newShift newIx
                else goBE (acc + fromIntegral digitGroup `unsafeShiftL` shift) limit newShift newIx
      | otherwise = finishBE acc limit shift ix
    finishBE :: Integer -> Int -> Int -> Int -> Integer
    finishBE acc limit shift ix
      | ix < limit = acc
      | otherwise =
          let digit = BS.index bs ix
              newShift = shift + 8
              newIx = ix - 1
           in if digit == 0
                then finishBE acc limit newShift newIx
                else finishBE (acc + fromIntegral digit `unsafeShiftL` shift) limit newShift newIx
    read64BE :: Int -> Word64
    read64BE endIx =
      fromIntegral (BS.index bs endIx)
        .|. (fromIntegral (BS.index bs (endIx - 1)) `unsafeShiftL` 8)
        .|. (fromIntegral (BS.index bs (endIx - 2)) `unsafeShiftL` 16)
        .|. (fromIntegral (BS.index bs (endIx - 3)) `unsafeShiftL` 24)
        .|. (fromIntegral (BS.index bs (endIx - 4)) `unsafeShiftL` 32)
        .|. (fromIntegral (BS.index bs (endIx - 5)) `unsafeShiftL` 40)
        .|. (fromIntegral (BS.index bs (endIx - 6)) `unsafeShiftL` 48)
        .|. (fromIntegral (BS.index bs (endIx - 7)) `unsafeShiftL` 56)
