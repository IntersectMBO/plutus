{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module Main (main) where

import Control.Monad (replicateM)
import Data.Bits (complement, popCount, zeroBits, (.&.))
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
import Implementations (chunkMap2, chunkMap3, chunkPopCount2, chunkPopCount3, chunkZipWith2, chunkZipWith3,
                        packZipWithBinary, rotateBS, rotateBSFast)
import System.IO.Unsafe (unsafeDupablePerformIO)
import System.Random.Stateful (mkStdGen, randomM, runStateGen_)
import Test.Tasty (withResource)
import Test.Tasty.Bench (Benchmark, bcompare, bench, bgroup, defaultMain, nfIO)

main :: IO ()
main = do
  setLocaleEncoding utf8
  defaultMain [
    bgroup bcompLabel . fmap (complementBench bcompLabel) $ sizes,
    bgroup bandLabel . fmap (andBench bandLabel) $ sizes,
    bgroup popCountLabel . fmap (popCountBench popCountLabel) $ sizes,
    bgroup rotateLabel . fmap (rotateVsPrescanBench rotateLabel) $ sizes,
    bgroup rotateLabel' . fmap (rotateFastVsSlow rotateLabel') $ sizes
    ]
  where
    sizes :: [Int]
    sizes = [1, 3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047]
    bandLabel :: String
    bandLabel = "Bitwise AND"
    bcompLabel :: String
    bcompLabel = "Bitwise complement"
    popCountLabel :: String
    popCountLabel = "Popcount"
    rotateLabel :: String
    rotateLabel = "Slow rotate versus prescan"
    rotateLabel' :: String
    rotateLabel' = "Bitwise rotate versus block rotate"

-- Benchmarks

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

popCountBench ::
  String ->
  Int ->
  Benchmark
popCountBench mainLabel len =
  withResource (mkUnaryArg len) noCleanup $ \xs ->
    let fLabel = "foldl'"
        cpLabel2 = "chunkPopCount2"
        cpLabel3 = "chunkPopCount3"
        testLabel = mainLabel <> ", length " <> show len
        matchLabel = "$NF == \"" <> fLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench fLabel . nfIO $ BS.foldl' (\acc w8 -> acc + popCount w8) 0 <$> xs,
        bcompare matchLabel . bench cpLabel2 . nfIO $ chunkPopCount2 <$> xs,
        bcompare matchLabel . bench cpLabel3 . nfIO $ chunkPopCount3 <$> xs
        ]

complementBench ::
  String ->
  Int ->
  Benchmark
complementBench mainLabel len =
  withResource (mkUnaryArg len) noCleanup $ \xs ->
    let mLabel = "map"
        cmLabel2 = "chunkedMap (2 blocks)"
        cmLabel2' = "chunkedMap (2 blocks, C)"
        cmLabel3 = "chunkMap (3 blocks)"
        testLabel = mainLabel <> ", length " <> show len
        matchLabel = "$NF == \"" <> mLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench mLabel . nfIO $ BS.map complement <$> xs,
        bcompare matchLabel . bench cmLabel2 . nfIO $ chunkMap2 complement complement <$> xs,
        bcompare matchLabel . bench cmLabel2' . nfIO $ ccomplement <$> xs,
        bcompare matchLabel . bench cmLabel3 . nfIO $ chunkMap3 complement complement complement <$> xs
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
