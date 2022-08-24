module Benches.Rotate (
  benches,
  ) where

import Data.Bits (bit, shiftR, testBit, zeroBits, (.|.))
import Data.Bool (bool)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Foldable (foldl')
import Data.Word (Word8)
import DataGen (mkUnaryArg, noCleanup, sizes)
import GHC.Exts (fromList)
import Test.Tasty (withResource)
import Test.Tasty.Bench (Benchmark, bench, bgroup, nfIO)

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
        testLabel = mainLabel <> ", length " <> show len in
      bgroup testLabel [
        bench naiveLabel . nfIO $ bitRotate (len * 4) <$> xs
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

bitAtWraparound :: ByteString -> Int -> Bool
bitAtWraparound bs i
  | i < 0 = bitAtWraparound bs (i + bitLength)
  | otherwise = let (bigIx, smallIx) = i `quotRem` 8
                    byte = BS.index bs bigIx in
      testBit byte $ shiftR 0x80 smallIx
  where
    bitLength :: Int
    bitLength = BS.length bs * 8
