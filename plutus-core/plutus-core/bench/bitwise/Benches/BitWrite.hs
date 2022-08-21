module Benches.BitWrite (
  benches
  ) where

import Control.Monad (guard)
import Data.Bits (clearBit, setBit, shiftR)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Internal (fromForeignPtr, mallocByteString)
import Data.ByteString.Unsafe (unsafeUseAsCStringLen)
import Data.Word (Word8)
import DataGen (mkUnaryArg, noCleanup, sizes)
import Foreign.C.Types (CBool (CBool), CSize (CSize), CUChar)
import Foreign.ForeignPtr (castForeignPtr, withForeignPtr)
import Foreign.Ptr (Ptr, castPtr)
import GHC.Exts (fromList, toList)
import System.IO.Unsafe (unsafeDupablePerformIO)
import Test.Tasty (withResource)
import Test.Tasty.Bench (Benchmark, bcompare, bench, bgroup, nfIO)

benches :: Benchmark
benches = bgroup "Worst-case bit write" $ benchBasic "Worst-case bit write" <$> sizes

-- Helpers

benchBasic ::
  String ->
  Int ->
  Benchmark
benchBasic mainLabel len =
  withResource (mkUnaryArg len) noCleanup $ \xs ->
    let naiveLabel = "ByteString ops"
        cnaiveLabel = "Naive C"
        cmemcpyLabel = "Memcpy C"
        testLabel = mainLabel <> ", length " <> show len
        matchLabel = "$NF == \"" <> naiveLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench naiveLabel . nfIO $ bitSet False (len - 1) <$> xs,
        bcompare matchLabel . bench cnaiveLabel . nfIO $ wrapper cBitSetNaive False (len - 1) <$> xs,
        bcompare matchLabel . bench cmemcpyLabel . nfIO $ wrapper cBitSetMemcpy False (len - 1) <$> xs
        ]

bitSet :: Bool -> Int -> ByteString -> Maybe ByteString
bitSet b ix bs = do
  guard (ix >= 0)
  guard (ix < bitLength)
  pure . fromList . fmap (uncurry go) . zip [0 ..] . toList $ bs
  where
    go :: Int -> Word8 -> Word8
    go candidateIx w8
      | candidateIx /= bigIx = w8
      | b = setBit w8 $ shiftR 0x80 smallIx
      | otherwise = clearBit w8 $ shiftR 0x80 smallIx
    bitLength :: Int
    bitLength = BS.length bs * 8
    bigIx :: Int
    bigIx = ix `quot` 8
    smallIx :: Int
    smallIx = ix `rem` 8

wrapper ::
  (CBool -> CSize -> Ptr CUChar -> Ptr CUChar -> CSize -> IO ()) ->
  Bool ->
  Int ->
  ByteString ->
  Maybe ByteString
wrapper f b ix bs = do
  guard (ix >= 0)
  guard (ix < bitLength)
  pure . unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ \(src, len) -> do
    fp <- mallocByteString len
    withForeignPtr fp $ \dst ->
      if b
      then f (CBool 1) (fromIntegral ix) dst (castPtr src) . fromIntegral $ len
      else f (CBool 0) (fromIntegral ix) dst (castPtr src) . fromIntegral $ len
    pure . fromForeignPtr (castForeignPtr fp) 0 $ len
  where
    bitLength :: Int
    bitLength = BS.length bs * 8

foreign import ccall unsafe "cbits.h c_bit_set_naive"
  cBitSetNaive ::
    CBool ->
    CSize ->
    Ptr CUChar ->
    Ptr CUChar ->
    CSize ->
    IO ()

foreign import ccall unsafe "cbits.h c_bit_set_memcpy"
  cBitSetMemcpy ::
    CBool ->
    CSize ->
    Ptr CUChar ->
    Ptr CUChar ->
    CSize ->
    IO ()
