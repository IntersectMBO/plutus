module Benches.BitRead (
  benches
  ) where

import Control.Monad (guard)
import Data.Bits (shiftR, testBit)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe (unsafeUseAsCStringLen)
import DataGen (mkUnaryArg, noCleanup, sizes)
import Foreign.C.Types (CBool (CBool), CSize (CSize), CUChar)
import Foreign.Ptr (Ptr, castPtr)
import System.IO.Unsafe (unsafeDupablePerformIO)
import Test.Tasty (withResource)
import Test.Tasty.Bench (Benchmark, bcompare, bench, bgroup, nfIO)

benches :: Benchmark
benches = bgroup "Basic bit read" $ benchBasic "Basic bit read" <$> sizes

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
        bench naiveLabel . nfIO $ bitAt (len - 1) <$> xs,
        bcompare matchLabel . bench cLabel . nfIO $ wrapper (len - 1) <$> xs
        ]

bitAt :: Int -> ByteString -> Maybe Bool
bitAt ix bs = do
  guard (ix >= 0)
  guard (ix < bitLength)
  let (bigIx, smallIx) = ix `quotRem` 8
  let byte = BS.index bs bigIx
  pure . testBit byte $ shiftR 0x80 smallIx
  where
    bitLength :: Int
    bitLength = BS.length bs * 8

wrapper :: Int -> ByteString -> Maybe Bool
wrapper ix bs = do
  guard (ix >= 0)
  guard (ix <= bitLength)
  let CBool res = unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ \(ptr, len) ->
                    pure . cBitAt (fromIntegral ix) (castPtr ptr) . fromIntegral $ len
  pure $ res /= 0
  where
    bitLength :: Int
    bitLength = BS.length bs * 8

foreign import ccall unsafe "cbits.h c_bit_at"
  cBitAt ::
    CSize ->
    Ptr CUChar ->
    CSize ->
    CBool
