-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Benches.Complement qualified as Complement
import Benches.Homogenous qualified as Homogenous
import Benches.Popcount qualified as Popcount
import Data.Bits (complement, zeroBits, (.&.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe (unsafePackMallocCStringLen, unsafeUseAsCStringLen)
import Data.Word (Word8)
import DataGen (mkBinaryArgs, mkUnaryArg, noCleanup, sizes)
import Foreign.C.Types (CSize (CSize), CUChar)
import Foreign.Marshal.Alloc (mallocBytes)
import Foreign.Ptr (Ptr, castPtr)
import GHC.Exts (fromListN)
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import Implementations (chunkZipWith2, chunkZipWith3, packZipWithBinary, rotateBS, rotateBSFast)
import System.IO.Unsafe (unsafeDupablePerformIO)
import Test.Tasty (testGroup, withResource)
import Test.Tasty.Bench (Benchmark, bcompare, bench, bgroup, defaultMain, nfIO)

main :: IO ()
main = do
  setLocaleEncoding utf8
  defaultMain [
    testGroup "Popcount" [
      Popcount.benches,
      Popcount.cBenches
      ],
    testGroup "Complement" [
      Complement.benches
      ],
    testGroup "Homogenous" [
      Homogenous.benches
      ],
    bgroup bandLabel . fmap (andBench bandLabel) $ sizes,
    bgroup rotateLabel . fmap (rotateVsPrescanBench rotateLabel) $ sizes,
    bgroup rotateLabel' . fmap (rotateFastVsSlow rotateLabel') $ sizes,
    bgroup bandLabel' . fmap (packedAndBench bandLabel') $ largerSizes,
    bgroup bandCOnlyLabel . fmap (andCOnlyBench bandCOnlyLabel) $ sizes
    ]
  where
    largerSizes :: [Int]
    largerSizes = [31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383, 32767]
    bandLabel :: String
    bandLabel = "Bitwise AND"
    bandLabel' :: String
    bandLabel' = "Packed bitwise AND"
    rotateLabel :: String
    rotateLabel = "Slow rotate versus prescan"
    rotateLabel' :: String
    rotateLabel' = "Bitwise rotate versus block rotate"
    bandCOnlyLabel :: String
    bandCOnlyLabel = "C bitwise AND"

-- Benchmarks

andCOnlyBench ::
  String ->
  Int ->
  Benchmark
andCOnlyBench mainLabel len =
  withResource (mkBinaryArgs len) noCleanup $ \xs ->
    let pzwLabel' = "packZipWith (C)"
        czwLabel2' = "chunkedZipWith (2 blocks, C)"
        czwLabel3' = "chunkedZipWith (3 blocks, C)"
        testLabel = mainLabel <> ", length " <> show len
        matchLabel = "$NF == \"" <> pzwLabel' <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench pzwLabel' . nfIO $ uncurry candBinaryNaive <$> xs,
        bcompare matchLabel . bench czwLabel2' . nfIO $ uncurry candBinary2 <$> xs,
        bcompare matchLabel . bench czwLabel3' . nfIO $ uncurry candBinary3 <$> xs
        ]

packedAndBench ::
  String ->
  Int ->
  Benchmark
packedAndBench mainLabel len =
  withResource (mkBinaryArgs len) noCleanup $ \xs ->
    let pzwLabel = "packZipWith"
        pzwLabel' = "packZipWith (C)"
        czwLabel2 = "chunkedZipWith (2 blocks)"
        czwLabel2' = "chunkedZipWith (2 blocks, C)"
        czwLabel3 = "chunkedZipWith (3 blocks)"
        czwLabel3' = "chunkedZipWith (3 blocks, C)"
        testLabel = mainLabel <> ", length " <> show len
        matchLabel = "$NF == \"" <> pzwLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench pzwLabel . nfIO $ uncurry (zipWithBinary (.&.)) <$> xs,
        bcompare matchLabel . bench pzwLabel' . nfIO $ uncurry candBinaryNaive <$> xs,
        bcompare matchLabel . bench czwLabel2 . nfIO $ uncurry (chunkZipWith2 (.&.) (.&.)) <$> xs,
        bcompare matchLabel . bench czwLabel2' . nfIO $ uncurry candBinary2 <$> xs,
        bcompare matchLabel . bench czwLabel3 . nfIO $ uncurry (chunkZipWith3 (.&.) (.&.) (.&.)) <$> xs,
        bcompare matchLabel . bench czwLabel3' . nfIO $ uncurry candBinary3 <$> xs
        ]

rotateFastVsSlow ::
  String ->
  Int ->
  Benchmark
rotateFastVsSlow mainLabel len =
  withResource (mkUnaryArg len) noCleanup $ \xs ->
    let rLabel = "rotate (bit-by-bit)"
        rLabel' = "rotate (block-optimized)"
        -- Next highest multiple of 8 of half our length, rounded down
        rotation = ((len `quot` 2) + 7) .&. negate 8
        testLabel = mainLabel <> ", length " <> show len <> ", rotation by " <> show rotation
        matchLabel = "$NF == \"" <> rLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench rLabel . nfIO $ rotateBS <$> xs <*> pure rotation,
        bcompare matchLabel . bench rLabel' . nfIO $ rotateBSFast <$> xs <*> pure rotation
        ]

rotateVsPrescanBench ::
  String ->
  Int ->
  Benchmark
rotateVsPrescanBench mainLabel len =
  withResource (mkUnaryArg len) noCleanup $ \xs ->
    let rLabel = "rotate (bit-by-bit)"
        pLabel = "prescan (naive)"
        rotation = len `quot` 2
        testLabel = mainLabel <> ", length " <> show len
        matchLabel = "$NF == \"" <> rLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench rLabel . nfIO $ rotateBS <$> xs <*> pure rotation,
        bcompare matchLabel . bench pLabel . nfIO $ (||) <$> (BS.all (== zeroBits) <$> xs) <*>
                                                             (BS.all (== complement zeroBits) <$> xs)
        ]

andBench ::
  String ->
  Int ->
  Benchmark
andBench mainLabel len =
  withResource (mkBinaryArgs len) noCleanup $ \xs ->
    let zwLabel = "zipWith"
        pzwLabel = "packZipWith"
        pzwLabel' = "packZipWith (C)"
        czwLabel2 = "chunkedZipWith (2 blocks)"
        czwLabel2' = "chunkedZipWith (2 blocks, C)"
        czwLabel3 = "chunkedZipWith (3 blocks)"
        czwLabel3' = "chunkedZipWith (3 blocks, C)"
        testLabel = mainLabel <> ", length " <> show len
        matchLabel = "$NF == \"" <> zwLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench zwLabel . nfIO $ uncurry (zipWithBinary (.&.)) <$> xs,
        bcompare matchLabel . bench pzwLabel . nfIO $ uncurry (packZipWithBinary (.&.)) <$> xs,
        bcompare matchLabel . bench pzwLabel' . nfIO $ uncurry candBinaryNaive <$> xs,
        bcompare matchLabel . bench czwLabel2 . nfIO $ uncurry (chunkZipWith2 (.&.) (.&.)) <$> xs,
        bcompare matchLabel . bench czwLabel2' . nfIO $ uncurry candBinary2 <$> xs,
        bcompare matchLabel . bench czwLabel3 . nfIO $ uncurry (chunkZipWith3 (.&.) (.&.) (.&.)) <$> xs,
        bcompare matchLabel . bench czwLabel3' . nfIO $ uncurry candBinary3 <$> xs
        ]

-- Helpers

-- Naive implementations for comparison
zipWithBinary ::
  (Word8 -> Word8 -> Word8) ->
  ByteString ->
  ByteString ->
  Maybe ByteString
zipWithBinary f bs bs'
  | len /= BS.length bs' = Nothing
  | otherwise = pure . fromListN len . BS.zipWith f bs $ bs'
  where
    len :: Int
    len = BS.length bs

-- Wrapper for raw C bitwise AND
candBinary2 :: ByteString -> ByteString -> Maybe ByteString
candBinary2 bs bs'
  | BS.length bs /= BS.length bs' = Nothing
  | otherwise = pure . unsafeDupablePerformIO .
    unsafeUseAsCStringLen bs $ \(src, len) ->
      unsafeUseAsCStringLen bs' $ \(src', _) -> do
        dst <- mallocBytes len
        candImplementation2 dst (castPtr src) (castPtr src') (fromIntegral len)
        unsafePackMallocCStringLen (castPtr dst, len)

-- Same as above, but 3-fold unroll
candBinary3 :: ByteString -> ByteString -> Maybe ByteString
candBinary3 bs bs'
  | BS.length bs /= BS.length bs' = Nothing
  | otherwise = pure . unsafeDupablePerformIO .
    unsafeUseAsCStringLen bs $ \(src, len) ->
      unsafeUseAsCStringLen bs' $ \(src', _) -> do
        dst <- mallocBytes len
        candImplementation3 dst (castPtr src) (castPtr src') (fromIntegral len)
        unsafePackMallocCStringLen (castPtr dst, len)

-- Same as above, but as obvious as possible
candBinaryNaive :: ByteString -> ByteString -> Maybe ByteString
candBinaryNaive bs bs'
  | BS.length bs /= BS.length bs' = Nothing
  | otherwise = pure . unsafeDupablePerformIO .
    unsafeUseAsCStringLen bs $ \(src, len) ->
      unsafeUseAsCStringLen bs' $ \(src', _) -> do
        dst <- mallocBytes len
        candImplementationNaive dst (castPtr src) (castPtr src') (fromIntegral len)
        unsafePackMallocCStringLen (castPtr dst, len)

foreign import ccall unsafe "cbits.h c_and_implementation_naive"
  candImplementationNaive ::
    Ptr CUChar ->
    Ptr CUChar ->
    Ptr CUChar ->
    CSize ->
    IO ()

foreign import ccall unsafe "cbits.h c_and_implementation"
  candImplementation2 ::
    Ptr CUChar ->
    Ptr CUChar ->
    Ptr CUChar ->
    CSize ->
    IO ()

foreign import ccall unsafe "cbits.h c_and_implementation_3"
  candImplementation3 ::
    Ptr CUChar ->
    Ptr CUChar ->
    Ptr CUChar ->
    CSize ->
    IO ()
