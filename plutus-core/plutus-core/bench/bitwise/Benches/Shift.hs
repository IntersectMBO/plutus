module Benches.Shift (
  benches,
  overlongBenches,
  byteStepBenches,
  ) where

import Data.Bits (bit, shiftR, testBit, zeroBits, (.|.))
import Data.Bool (bool)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Internal (fromForeignPtr, mallocByteString)
import Data.ByteString.Unsafe (unsafeUseAsCStringLen)
import Data.Foldable (foldl')
import Data.Word (Word8)
import DataGen (mkUnaryArg, noCleanup, sizes)
import Foreign.C.Types (CInt (CInt), CSize (CSize), CUChar)
import Foreign.ForeignPtr (castForeignPtr, withForeignPtr)
import Foreign.Ptr (Ptr, castPtr)
import GHC.Exts (fromList)
import System.IO.Unsafe (unsafeDupablePerformIO)
import Test.Tasty (withResource)
import Test.Tasty.Bench (Benchmark, bcompare, bench, bgroup, nfIO)

benches :: Benchmark
benches = bgroup "Basic bitwise shift" $ benchBasic "Basic bitwise shift" <$> sizes

overlongBenches :: Benchmark
overlongBenches = bgroup "Overlong bitwise shift" $ benchOverlong "Overlong bitwise shift" <$> sizes

byteStepBenches :: Benchmark
byteStepBenches = bgroup "Byte bitwise shift" $ benchByteShift "Byte bitwise shift" <$> sizes

-- Helpers

benchByteShift ::
  String ->
  Int ->
  Benchmark
benchByteShift mainLabel len =
  withResource (mkUnaryArg len) noCleanup $ \xs ->
    let noPrecheckByteLabel = "No precheck, byte shift"
        noPrecheckNotLabel = "No precheck, non-byte shift"
        precheckByteLabel = "Precheck, byte shift"
        precheckNotLabel = "Precheck, non-byte shift"
        precheckCByteLabel = "Precheck in C, byte shift"
        precheckCNotLabel = "Precheck in C, non-byte shift"
        testLabel = mainLabel <> ", length " <> show len
        matchLabelByte = "$NF == \"" <> noPrecheckByteLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\""
        matchLabelNot = "$NF == \"" <> noPrecheckNotLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench noPrecheckByteLabel . nfIO $ bitShift ((len - 1) * 8) <$> xs,
        bench noPrecheckNotLabel . nfIO $ bitShift (len * 4 - 1) <$> xs,
        bcompare matchLabelByte . bench precheckByteLabel . nfIO $ precheckByte bitShift ((len - 1) * 8) <$> xs,
        bcompare matchLabelNot . bench precheckNotLabel . nfIO $ precheckByte bitShift (len * 4 - 1) <$> xs,
        bcompare matchLabelByte . bench precheckCByteLabel . nfIO $ precheckByteC bitShift ((len - 1) * 8) <$> xs,
        bcompare matchLabelNot . bench precheckCNotLabel . nfIO $ precheckByteC bitShift (len * 4 - 1) <$> xs
        ]

benchOverlong ::
  String ->
  Int ->
  Benchmark
benchOverlong mainLabel len =
  withResource (mkUnaryArg len) noCleanup $ \xs ->
    let noPrecheckOverlongLabel = "No precheck, overlong"
        noPrecheckNotLabel = "No precheck, not overlong"
        precheckOverlongLabel = "Precheck, overlong"
        precheckNotLabel = "Precheck, not overlong"
        testLabel = mainLabel <> ", length " <> show len
        matchLabelOverlong = "$NF == \"" <> noPrecheckOverlongLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\""
        matchLabelNot = "$NF == \"" <> noPrecheckNotLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench noPrecheckOverlongLabel . nfIO $ bitShift (len * 16) <$> xs,
        bench noPrecheckNotLabel . nfIO $ bitShift (len * 4) <$> xs,
        bcompare matchLabelOverlong . bench precheckOverlongLabel . nfIO $ precheckOverlong bitShift (len * 16) <$> xs,
        bcompare matchLabelNot . bench precheckNotLabel . nfIO $ precheckOverlong bitShift (len * 4) <$> xs
        ]

benchBasic ::
  String ->
  Int ->
  Benchmark
benchBasic mainLabel len =
  withResource (mkUnaryArg len) noCleanup $ \xs ->
    let naiveLabel = "ByteString ops"
        testLabel = mainLabel <> ", length " <> show len in
      bgroup testLabel [
        bench naiveLabel . nfIO $ bitShift (len * 4) <$> xs
        ]

precheckByte ::
  (Int -> ByteString -> ByteString) ->
  Int ->
  ByteString ->
  ByteString
precheckByte f i bs = case i `quotRem` 8 of
  (i', 0) -> fromList $ go . (`subtract` i') <$> [0 .. len - 1]
  _       -> f i bs
  where
    go :: Int -> Word8
    go readIx
      | readIx < 0 = zeroBits
      | readIx >= len = zeroBits
      | otherwise = BS.index bs readIx
    len :: Int
    len = BS.length bs

precheckByteC ::
  (Int -> ByteString -> ByteString) ->
  Int ->
  ByteString ->
  ByteString
precheckByteC f i bs = case i `quotRem` 8 of
  (i', 0) -> unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ \(src, len) -> do
    fp <- mallocByteString len
    withForeignPtr fp $ \dst -> cShiftBytes (fromIntegral i') dst (castPtr src) . fromIntegral $ len
    pure . fromForeignPtr (castForeignPtr fp) 0 $ len
  _ -> f i bs

precheckOverlong ::
  (Int -> ByteString -> ByteString) ->
  Int ->
  ByteString ->
  ByteString
precheckOverlong f i bs
  | abs i >= bitLen = BS.replicate len zeroBits
  | otherwise = f i bs
  where
    len :: Int
    len = BS.length bs
    bitLen :: Int
    bitLen = len * 8

bitShift :: Int -> ByteString -> ByteString
bitShift i bs = case signum i of
  0 -> bs
  _ -> fromList $ go <$> [0 .. BS.length bs - 1]
  where
    go :: Int -> Word8
    go byteIx = let bitIxes = (\ix -> 8 * byteIx - i + ix) <$> [0 .. 7]
                    bits = bitAtClipping bs <$> bitIxes
                    zipped = zip [7, 6 .. 0] bits in
      foldl' (\acc (pos, b) -> acc .|. bool zeroBits (bit pos) b) zeroBits zipped

bitAtClipping :: ByteString -> Int -> Bool
bitAtClipping bs i
  | i < 0 = False
  | i >= bitLength = False
  | otherwise = let (bigIx, smallIx) = i `quotRem` 8
                    byte = BS.index bs bigIx in
      testBit byte $ shiftR 0x80 smallIx
  where
    bitLength :: Int
    bitLength = BS.length bs * 8

foreign import ccall unsafe "cbits.h  c_shift_bytes"
  cShiftBytes ::
    CInt ->
    Ptr CUChar ->
    Ptr CUChar ->
    CSize ->
    IO ()
