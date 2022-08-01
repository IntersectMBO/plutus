{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module Main (main) where

import Bitwise.Internal (chunkMap2, chunkZipWith2, chunkZipWith3, packZipWithBinary)
import Control.Monad (replicateM)
import Data.Bits (complement, (.&.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe (unsafePackMallocCStringLen, unsafeUseAsCStringLen)
import Data.Kind (Type)
import Data.Word (Word8)
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
    bgroup bcompLabel . fmap (complementBench bcompLabel) $ sizes,
    bgroup bandLabel . fmap (andBench bandLabel) $ sizes
    ]
  where
    sizes :: [Int]
    sizes = [1, 3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047]
    bandLabel :: String
    bandLabel = "Bitwise AND"
    bcompLabel :: String
    bcompLabel = "Bitwise complement"

-- Benchmarks

complementBench ::
  String ->
  Int ->
  Benchmark
complementBench mainLabel len =
  withResource (mkUnaryArg len) noCleanup $ \xs ->
    let mLabel = "map"
        cmLabel2 = "chunkedMap (2 blocks)"
        cmLabel2' = "chunkedMap (2 blocks, C)"
        testLabel = mainLabel <> ", length " <> show len
        matchLabel = "$NF == \"" <> mLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench mLabel . nfIO $ BS.map complement <$> xs,
        bcompare matchLabel . bench cmLabel2 . nfIO $ chunkMap2 complement complement <$> xs,
        bcompare matchLabel . bench cmLabel2' . nfIO $ ccomplement <$> xs
        ]

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

-- Generators

mkUnaryArg :: Int -> IO ByteString
mkUnaryArg len = pure . runStateGen_ (mkStdGen 42) $ \gen ->
  fromListN len <$> replicateM len (randomM gen)

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

-- Wrapper for raw C bitwise complement
ccomplement :: ByteString -> ByteString
ccomplement bs = unsafeDupablePerformIO .
  unsafeUseAsCStringLen bs $ \(src, len) -> do
    dst <- mallocBytes len
    ccomplementImplementation dst (castPtr src) (fromIntegral len)
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

foreign import ccall unsafe "cbits.h c_complement_implementation"
  ccomplementImplementation ::
    Ptr CUChar ->
    Ptr CUChar ->
    CSize ->
    IO ()
