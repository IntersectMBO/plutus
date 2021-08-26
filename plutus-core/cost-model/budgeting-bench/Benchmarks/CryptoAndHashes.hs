{-# LANGUAGE OverloadedStrings #-}

module Benchmarks.CryptoAndHashes (makeBenchmarks) where

import           Benchmarks.Common

import           PlutusCore

import           Criterion.Main
import qualified Data.ByteString       as BS
import           System.Random         (StdGen)

import qualified Hedgehog              as HH
import qualified Hedgehog.Internal.Gen as HH
import qualified Hedgehog.Range        as HH.Range


-- *** DUPLICATED

byteStringSizes :: [Integer]
byteStringSizes = fmap (100*) [0..100]
-- 0--80000 bytes

byteStringsToBench :: HH.Seed -> [BS.ByteString]
byteStringsToBench seed = (makeSizedBytestring seed . fromInteger) <$> byteStringSizes

makeSizedBytestring :: HH.Seed -> Int -> BS.ByteString
makeSizedBytestring seed e = genSample seed (HH.bytes (HH.Range.singleton e))

benchByteStringOneArgOp :: DefaultFun -> Benchmark
benchByteStringOneArgOp name =
    bgroup (show name) $ fmap mkBM (byteStringsToBench seedA)
           where mkBM b = benchDefault (showMemoryUsage b) $ mkApp1 name b


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
    bgroup (show name) $ fmap mkBM (byteStringsToBench seedA)
           where name = VerifySignature
                 mkBM b = benchDefault (showMemoryUsage b) $ mkApp3 name pubKey b sig


makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks _gen =  [benchVerifySignature]
                    <> (benchByteStringOneArgOp <$> [ Sha2_256, Sha3_256, Blake2b_256 ])




