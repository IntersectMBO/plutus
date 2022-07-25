{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module Main (main) where

import Bitwise.PackZipWith (packZipWithBinary)
import Control.Monad (replicateM)
import Data.Bits ((.&.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Kind (Type)
import Data.Word (Word8)
import GHC.Exts (fromListN)
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import System.Random.Stateful (mkStdGen, randomM, runStateGen_)
import Test.Tasty (withResource)
import Test.Tasty.Bench (Benchmark, bcompare, bench, bgroup, defaultMain, nfIO)

main :: IO ()
main = do
  setLocaleEncoding utf8
  defaultMain [
    bgroup "Bitwise AND" . fmap bitwiseAndBench $ [1, 3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047]
    ]

-- Benchmarks

bitwiseAndBench :: Int -> Benchmark
bitwiseAndBench len = withResource (mkBinaryArgs len) noCleanup $ \xs ->
  let label = "zipWith"
      label' = "packZipWith"
      label'' = "hybrid"
      testLabel = "Bitwise AND, length " <> show len
      matchLabel = "$NF == \"" <> label <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
    bgroup testLabel [
      bench label . nfIO $ uncurry (zipWithBinary (.&.)) <$> xs,
      bcompare matchLabel . bench label' . nfIO $ uncurry (packZipWithBinary (.&.)) <$> xs,
      bcompare matchLabel . bench label'' . nfIO $ uncurry (hybridBinary (.&.)) <$> xs
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

-- Hybrid to try and get the best of both
hybridBinary ::
  (Word8 -> Word8 -> Word8) ->
  ByteString ->
  ByteString ->
  Maybe ByteString
hybridBinary f bs bs'
  | max (BS.length bs) (BS.length bs') < 16 = zipWithBinary f bs bs'
  | otherwise = packZipWithBinary f bs bs'
