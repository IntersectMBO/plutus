{-# LANGUAGE BangPatterns #-}

module Benches.Convert (
  benchesBSToI,
  ) where

import Control.Monad (guard)
import Data.Bits (unsafeShiftL)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe (unsafeUseAsCStringLen)
import Data.Word (Word16, Word32, Word64, Word8)
import DataGen (mkUnaryArg, noCleanup, sizes)
import Foreign.C.Types (CChar)
import Foreign.Ptr (Ptr)
import Foreign.Storable (peekByteOff)
import System.IO.Unsafe (unsafeDupablePerformIO)
import Test.Tasty (withResource)
import Test.Tasty.Bench (Benchmark, bcompare, bench, bgroup, nfIO)

benchesBSToI :: Benchmark
benchesBSToI = bgroup "Basic ByteString to Integer conversion" $
  benchBSToI "Basic ByteString to Integer conversion" <$> sizes

-- Helpers

benchBSToI ::
  String ->
  Int ->
  Benchmark
benchBSToI mainLabel len =
  withResource (mkUnaryArg len) noCleanup $ \xs ->
    let naiveLabel = "scan backwards"
        forwardsLabel = "scan forwards"
        shiftLabel = "scan backwards with shifts"
        blockLabel = "scan backwards in blocks with shifts"
        forwardsShiftLabel = "scan forwards with shifts"
        testLabel = mainLabel <> ", length " <> show len
        matchLabel = "$NF == \"" <> naiveLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench naiveLabel . nfIO $ bsToI <$> xs,
        bcompare matchLabel . bench forwardsLabel . nfIO $ bsToIForward <$> xs,
        bcompare matchLabel . bench shiftLabel . nfIO $ bsToIShift <$> xs,
        bcompare matchLabel . bench forwardsShiftLabel . nfIO $ bsToIShiftForward <$> xs,
        bcompare matchLabel . bench blockLabel . nfIO $ bsToIShiftBlock <$> xs
        ]

-- Implementations

bsToI :: ByteString -> Maybe Integer
bsToI bs = do
  guard (len > 0)
  pure . go 0 1 $ len - 1
  where
    len :: Int
    len = BS.length bs
    go :: Integer -> Integer -> Int -> Integer
    go !acc !mult !ix = let limb :: Integer = fromIntegral . BS.index bs $ ix
                            limbValue = limb * mult
                            acc' = acc + limbValue in
                      if ix == 0
                      then acc'
                      else go acc' (mult * 256) $ ix - 1

bsToIForward :: ByteString -> Maybe Integer
bsToIForward bs = do
  guard (len > 0)
  pure . snd . BS.foldl' go (256 ^ (len - 1), 0) $ bs
  where
    len :: Int
    len = BS.length bs
    go :: (Integer, Integer) -> Word8 -> (Integer, Integer)
    go (mult, acc) w8 = let limbValue = fromIntegral w8 * mult in
      (mult `quot` 256, acc + limbValue)

bsToIShift :: ByteString -> Maybe Integer
bsToIShift bs = do
  guard (len > 0)
  pure . go 0 0 $ len - 1
  where
    len :: Int
    len = BS.length bs
    go :: Integer -> Int -> Int -> Integer
    go !acc !shift !ix = let limb :: Integer = fromIntegral . BS.index bs $ ix
                             limbValue = limb `unsafeShiftL` shift
                             acc' = acc + limbValue in
                      if ix == 0
                      then acc'
                      else go acc' (shift + 8) $ ix - 1

bsToIShiftBlock :: ByteString -> Maybe Integer
bsToIShiftBlock bs = do
  guard (len > 0)
  pure . unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ \(p, _) -> do
    go p 0 0 $ len - 1
  where
    len :: Int
    len = BS.length bs
    go :: Ptr CChar -> Integer -> Int -> Int -> IO Integer
    go p !acc !shift !ix
      | ix >= 7 = do
          w64 :: Word64 <- peekByteOff p (ix - 7)
          let limb :: Integer = fromIntegral w64
          let limbValue = limb `unsafeShiftL` shift
          go p (acc + limbValue) (shift + 64) $ ix - 8
      | ix >= 3 = do
          w32 :: Word32 <- peekByteOff p (ix - 3)
          let limb :: Integer = fromIntegral w32
          let limbValue = limb `unsafeShiftL` shift
          go p (acc + limbValue) (shift + 32) $ ix - 4
      | ix >= 1 = do
          w16 :: Word16 <- peekByteOff p (ix - 1)
          let limb :: Integer = fromIntegral w16
          let limbValue = limb `unsafeShiftL` shift
          go p (acc + limbValue) (shift + 16) $ ix - 2
      | ix == 0 = do
          w8 :: Word8 <- peekByteOff p ix
          let limb :: Integer = fromIntegral w8
          let limbValue = limb `unsafeShiftL` shift
          pure $ acc + limbValue
      | otherwise = pure acc

bsToIShiftForward :: ByteString -> Maybe Integer
bsToIShiftForward bs = do
  guard (len > 0)
  pure . snd . BS.foldl' go ((len - 1) * 8, 0) $ bs
  where
    len :: Int
    len = BS.length bs
    go :: (Int, Integer) -> Word8 -> (Int, Integer)
    go (shift, acc) w8 = let limbValue = fromIntegral w8 `unsafeShiftL` shift in
      (shift - 8, acc + limbValue)

