{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module Main (main) where

import Bitwise.ChunkZipWith (chunkZipWith2, chunkZipWith3)
import Bitwise.PackZipWith (packZipWithBinary)
import Control.Monad (replicateM)
import Data.Bits (xor, (.&.), (.|.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe (unsafePackMallocCStringLen, unsafeUseAsCStringLen)
import Data.Kind (Type)
import Data.WideWord.Word256 (Word256)
import Data.Word (Word64, Word8)
import Foreign.C.Types (CSize (CSize), CUChar)
import Foreign.Marshal.Alloc (mallocBytes)
import Foreign.Ptr (Ptr, castPtr)
import GHC.Exts (fromListN)
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import System.IO.Unsafe (unsafeDupablePerformIO)
import System.Random.Stateful (mkStdGen, randomM, runStateGen_)
import Test.Tasty (withResource)
import Test.Tasty.Bench (Benchmark, bcompare, bench, bgroup, defaultMain, nfIO)

main :: IO ()
main = do
  setLocaleEncoding utf8
  defaultMain [
    bgroup bandLabel . fmap (andBench bandLabel) $ sizes,
    bgroup biorLabel . fmap (binaryOpBench biorLabel (.|.) (.|.) (.|.)) $ sizes,
    bgroup bxorLabel . fmap (binaryOpBench bxorLabel xor xor xor) $ sizes
    ]
  where
    sizes :: [Int]
    sizes = [1, 3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047]
    bandLabel :: String
    bandLabel = "Bitwise AND"
    biorLabel :: String
    biorLabel = "Bitwise IOR"
    bxorLabel :: String
    bxorLabel = "Bitwise XOR"

-- Benchmarks

andBench ::
  String ->
  Int ->
  Benchmark
andBench mainLabel len =
  withResource (mkBinaryArgs len) noCleanup $ \xs ->
    let zwLabel = "zipWith"
        pzwLabel = "packZipWith"
        czwLabel2 = "chunkedZipWith (2 blocks)"
        czwLabel2' = "chunkedZipWith (2 blocks, C)"
        czwLabel3 = "chunkedZipWith (3 blocks)"
        czwLabel3' = "chunkedZipWith (3 blocks, C)"
        testLabel = mainLabel <> ", length " <> show len
        matchLabel = "$NF == \"" <> zwLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench zwLabel . nfIO $ uncurry (zipWithBinary (.&.)) <$> xs,
        bcompare matchLabel . bench pzwLabel . nfIO $ uncurry (packZipWithBinary (.&.)) <$> xs,
        bcompare matchLabel . bench czwLabel2 . nfIO $ uncurry (chunkZipWith2 (.&.) (.&.)) <$> xs,
        bcompare matchLabel . bench czwLabel2' . nfIO $ uncurry candBinary2 <$> xs,
        bcompare matchLabel . bench czwLabel3 . nfIO $ uncurry (chunkZipWith3 (.&.) (.&.) (.&.)) <$> xs,
        bcompare matchLabel . bench czwLabel3' . nfIO $ uncurry candBinary3 <$> xs
        ]

binaryOpBench ::
  String ->
  (Word8 -> Word8 -> Word8) ->
  (Word64 -> Word64 -> Word64) ->
  (Word256 -> Word256 -> Word256) ->
  Int ->
  Benchmark
binaryOpBench mainLabel f f' f'' len =
  withResource (mkBinaryArgs len) noCleanup $ \xs ->
    let zwLabel = "zipWith"
        pzwLabel = "packZipWith"
        czwLabel = "chunkedZipWith (2 blocks)"
        czwLabel' = "chunkedZipWith (3 blocks)"
        testLabel = mainLabel <> ", length " <> show len
        matchLabel = "$NF == \"" <> zwLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench zwLabel . nfIO $ uncurry (zipWithBinary f) <$> xs,
        bcompare matchLabel . bench pzwLabel . nfIO $ uncurry (packZipWithBinary f) <$> xs,
        bcompare matchLabel . bench czwLabel . nfIO $ uncurry (chunkZipWith2 f f') <$> xs,
        bcompare matchLabel . bench czwLabel' . nfIO $ uncurry (chunkZipWith3 f f' f'') <$> xs
        ]

-- Generators

mkBinaryArgs :: Int -> IO (ByteString, ByteString)
mkBinaryArgs len = pure . runStateGen_ (mkStdGen 42) $ \gen ->
  (,) <$> (fromListN len <$> replicateM len (randomM gen)) <*>
          (fromListN len <$> replicateM len (randomM gen))

-- Helpers

noCleanup :: forall (a :: Type) . a -> IO ()
noCleanup = const (pure ())

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
