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
import Data.Kind (Type)
import Data.WideWord.Word256 (Word256)
import Data.Word (Word64, Word8)
import GHC.Exts (fromListN)
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import System.Random.Stateful (mkStdGen, randomM, runStateGen_)
import Test.Tasty (withResource)
import Test.Tasty.Bench (Benchmark, bcompare, bench, bgroup, defaultMain, nfIO)

main :: IO ()
main = do
  setLocaleEncoding utf8
  defaultMain [
    bgroup bandLabel . fmap (binaryOpBench bandLabel (.&.) (.&.) (.&.)) $ sizes,
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
