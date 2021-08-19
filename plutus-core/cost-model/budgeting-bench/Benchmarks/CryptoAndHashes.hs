{-# LANGUAGE OverloadedStrings #-}

module Benchmarks.CryptoAndHashes (makeBenchmarks) where

import           Benchmarks.Common

import           PlutusCore                             as PLC
import           PlutusCore.Evaluation.Machine.ExMemory

import           Criterion.Main
import qualified Data.ByteString                        as BS
import           Data.Functor                           ((<&>))
import           System.Random                          (StdGen)

import qualified Hedgehog                               as HH
import qualified Hedgehog.Internal.Gen                  as HH
import qualified Hedgehog.Range                         as HH.Range


-- *** DUPLICATED

byteStringSizes :: [Integer]
byteStringSizes = integerPower 2 <$> [1..20::Integer]

makeSizedBytestring :: HH.Seed -> Int -> (BS.ByteString, ExMemory)
makeSizedBytestring seed e = let x = genSample seed (HH.bytes (HH.Range.singleton e)) in (x, memoryUsage x)

seedA :: HH.Seed
seedA = HH.Seed 42 43


---------------- Verify signature ----------------

-- for VerifySignature, for speed purposes, it shouldn't matter if the sig / pubkey are correct
sig :: BS.ByteString
sig = "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"

pubKey :: BS.ByteString
pubKey = "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"

-- The sizes of the signature and the key are fixed (64 and 32 bytes) so we don't include
-- them in the benchmark name.  However, in models.R we still have to remove the overhead
-- for a three-argument function.
benchVerifySignature :: Benchmark
benchVerifySignature =
    bgroup (show name) $
        bs <&> (\(x, xmem) ->
            benchDefault (show xmem) $ mkApp3 name pubKey x sig
        )
    where
        name = VerifySignature
        bs = (makeSizedBytestring seedA . fromInteger) <$> byteStringSizes


makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks _gen = [benchVerifySignature]
