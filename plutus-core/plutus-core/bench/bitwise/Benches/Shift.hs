module Benches.Shift (
  benches,
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

-- Helpers

benchBasic ::
  String ->
  Int ->
  Benchmark
benchBasic mainLabel len =
  withResource (mkUnaryArg len) noCleanup $ \xs ->
    let naiveLabel = "ByteString ops"
        cLabel = "C"
        testLabel = mainLabel <> ", length " <> show len
        matchLabel = "$NF == \"" <> naiveLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench naiveLabel . nfIO $ bitShift (len * 4) <$> xs,
        bcompare matchLabel . bench cLabel . nfIO $ bitShiftC (len * 4) <$> xs
        ]

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

bitShiftC :: Int -> ByteString -> ByteString
bitShiftC i bs = case signum i of
  0 -> bs
  _ -> unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ \(src, len) -> do
    fp <- mallocByteString len
    withForeignPtr fp $ \dst ->
      cShiftBits (fromIntegral i) dst (castPtr src) . fromIntegral $ len
    pure . fromForeignPtr (castForeignPtr fp) 0 $ len

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

foreign import ccall unsafe "cbits.h c_shift_bits"
  cShiftBits ::
    CInt ->
    Ptr CUChar ->
    Ptr CUChar ->
    CSize ->
    IO ()
