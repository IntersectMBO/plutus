module Benches.Rotate (
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
benches = bgroup "Basic bitwise rotate" $ benchBasic "Basic bitwise rotate" <$> sizes

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
        bench naiveLabel . nfIO $ bitRotate (len * 4) <$> xs,
        bcompare matchLabel . bench cLabel . nfIO $ bitRotateC (len * 4) <$> xs
        ]

bitRotate :: Int -> ByteString -> ByteString
bitRotate i bs
  | bitLen == 0 = bs
  | otherwise = case i `rem` bitLen of
      0 -> bs -- nothing to do
      j -> fromList $ go j <$> [0 .. BS.length bs - 1]
  where
    bitLen :: Int
    bitLen = BS.length bs * 8
    go :: Int -> Int -> Word8
    go j byteIx = let bitIxes = (\ix -> 8 * byteIx - j + ix) <$> [0 .. 7]
                      bits = bitAtWraparound bs <$> bitIxes
                      zipped = zip [7, 6 .. 0] bits in
      foldl' (\acc (pos, b) -> acc .|. bool zeroBits (bit pos) b) zeroBits zipped

bitRotateC :: Int -> ByteString -> ByteString
bitRotateC i bs
  | bitLen == 0 = bs
  | otherwise = case i `rem` bitLen of
      0 -> bs -- nothing to do
      j -> unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ \(src, len) -> do
        fp <- mallocByteString len
        withForeignPtr fp $ \dst ->
          cRotateBits (fromIntegral j) dst (castPtr src) . fromIntegral $ len
        pure . fromForeignPtr (castForeignPtr fp) 0 $ len
  where
    bitLen :: Int
    bitLen = BS.length bs * 8

bitAtWraparound :: ByteString -> Int -> Bool
bitAtWraparound bs i
  | i < 0 = bitAtWraparound bs (i + bitLength)
  | otherwise = let (bigIx, smallIx) = i `quotRem` 8
                    byte = BS.index bs bigIx in
      testBit byte $ shiftR 0x80 smallIx
  where
    bitLength :: Int
    bitLength = BS.length bs * 8

foreign import ccall unsafe "cbits.h c_rotate_bits"
  cRotateBits ::
    CInt ->
    Ptr CUChar ->
    Ptr CUChar ->
    CSize ->
    IO ()
