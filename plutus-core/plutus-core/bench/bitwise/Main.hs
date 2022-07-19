{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE OverloadedStrings #-}
-- Needed for tasty-bench
{-# OPTIONS_GHC -Wno-orphans #-}

module Main (main) where

import Bitwise (andByteString, iorByteString, xorByteString)
import Control.DeepSeq (NFData (rnf))
import Control.Monad (replicateM)
import Control.Monad.ST (ST)
import Control.Monad.Trans.State.Strict (StateT)
import Data.Bits (xor, (.&.), (.|.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Kind (Type)
import Data.Text (pack)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import GHC.Exts (fromListN, toList)
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import PlutusCore.Builtin.Emitter (Emitter, emit, runEmitter)
import PlutusCore.Evaluation.Result (EvaluationResult (EvaluationFailure, EvaluationSuccess))
import System.Random.Stateful (StateGenM, StdGen, mkStdGen, randomM, runStateGenST_)
import Test.Tasty.Bench (Benchmark, bcompare, bench, bgroup, defaultMain, nf)

main :: IO ()
main = do
  setLocaleEncoding utf8
  defaultMain [
    bgroup "Bitwise AND" bandBenches,
    bgroup "Bitwise IOR" biorBenches,
    bgroup "Bitwise XOR" bxorBenches
    ]

-- Benchmarks

bandBenches :: [Benchmark]
bandBenches = toList sampleData >>= go
  where
    go :: (Int, ByteString, ByteString) -> [Benchmark]
    go (len, bs, bs') =
      let label = "naive, length " <> show len
          label' = "optimized, length " <> show len
          matchLabel = "$NF == \"" <> label' <> "\" && $(NF -1) == \"Bitwise AND\"" in
      [
        bench label' . nf (andByteString bs) $ bs',
        bcompare matchLabel . bench label . nf (naiveAnd bs) $ bs'
      ]

biorBenches :: [Benchmark]
biorBenches = toList sampleData >>= go
  where
    go :: (Int, ByteString, ByteString) -> [Benchmark]
    go (len, bs, bs') =
      let label = "naive, length " <> show len
          label' = "optimized, length " <> show len
          matchLabel = "$NF == \"" <> label' <> "\" && $(NF -1) == \"Bitwise IOR\"" in
      [
        bench label' . nf (iorByteString bs) $ bs',
        bcompare matchLabel . bench label . nf (naiveIor bs) $ bs'
      ]

bxorBenches :: [Benchmark]
bxorBenches = toList sampleData >>= go
  where
    go :: (Int, ByteString, ByteString) -> [Benchmark]
    go (len, bs, bs') =
      let label = "naive, length " <> show len
          label' = "optimized, length " <> show len
          matchLabel = "$NF == \"" <> label' <> "\" && $(NF -1) == \"Bitwise XOR\"" in
      [
        bench label' . nf (xorByteString bs) $ bs',
        bcompare matchLabel . bench label . nf (naiveXor bs) $ bs'
      ]


-- Naive implementations for comparison

naiveAnd :: ByteString -> ByteString -> Emitter (EvaluationResult ByteString)
naiveAnd bs bs'
  | BS.length bs /= BS.length bs' = do
      emit "andByteString failed"
      emit "Reason: mismatched argument lengths"
      emit $ "Length of first argument: " <> (pack . show . BS.length $ bs)
      emit $ "Length of second argument: " <> (pack . show . BS.length $ bs')
      pure EvaluationFailure
  | otherwise = do
      let len = BS.length bs
      pure . pure . fromListN len . BS.zipWith (.&.) bs $ bs'

naiveIor :: ByteString -> ByteString -> Emitter (EvaluationResult ByteString)
naiveIor bs bs'
  | BS.length bs /= BS.length bs' = do
      emit "iorByteString failed"
      emit "Reason: mismatched argument lengths"
      emit $ "Length of first argument: " <> (pack . show . BS.length $ bs)
      emit $ "Length of second argument: " <> (pack . show . BS.length $ bs')
      pure EvaluationFailure
  | otherwise = do
      let len = BS.length bs
      pure . pure . fromListN len . BS.zipWith (.|.) bs $ bs'

naiveXor :: ByteString -> ByteString -> Emitter (EvaluationResult ByteString)
naiveXor bs bs'
  | BS.length bs /= BS.length bs' = do
      emit "xorByteString failed"
      emit "Reason: mismatched argument lengths"
      emit $ "Length of first argument: " <> (pack . show . BS.length $ bs)
      emit $ "Length of second argument: " <> (pack . show . BS.length $ bs')
      pure EvaluationFailure
  | otherwise = do
      let len = BS.length bs
      pure . pure . fromListN len . BS.zipWith xor bs $ bs'

-- Data

-- Note: Methodology for benchmarking data sizes
--
-- As the on-chain memory limit is approximately 13KiB, which has to include the
-- code as well as the arguments, we consider an upper limit of usefulness on
-- the length of a ByteString to be about 2KiB, which is 2048 bytes. Likewise,
-- ByteStrings whose length is significantly shorter than 64 bytes fit into a
-- single cache line on basically any architecture we care about, which means
-- that the differences in implementation strategies would probably be fairly
-- minimal.
--
-- On the basis of the above, we generate test data pairs of the following
-- byte lengths (for each element of each pair):
--
-- * 64
-- * 128
-- * 256
-- * 512
-- * 1024
-- * 2048

sampleData :: Vector (Int, ByteString, ByteString)
sampleData =
  runStateGenST_ (mkStdGen 42) (\gen -> Vector.generateM 6 (go gen))
  where
    go :: forall (s :: Type) .
      StateGenM StdGen ->
      Int ->
      StateT StdGen (ST s) (Int, ByteString, ByteString)
    go gen ix = do
      let len = 64 * (2 ^ ix)
      leftRes <- fromListN len <$> replicateM len (randomM gen)
      rightRes <- fromListN len <$> replicateM len (randomM gen)
      pure (len, leftRes, rightRes)

-- We unfortunately need this orphan or tasty-bench won't do much for us
instance NFData (Emitter (EvaluationResult ByteString)) where
  rnf x = case runEmitter x of
    (res, logs) -> case res of
      EvaluationFailure   -> rnf logs
      EvaluationSuccess y -> seq y . rnf $ logs
