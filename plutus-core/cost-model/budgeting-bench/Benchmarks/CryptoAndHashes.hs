{-# LANGUAGE OverloadedStrings #-}

module Benchmarks.CryptoAndHashes (makeBenchmarks) where

import Common
import Generators

import PlutusCore

import Criterion.Main
import Data.ByteString qualified as BS
import System.Random (StdGen)

import Hedgehog qualified as H
import Hedgehog.Internal.Gen qualified as G
import Hedgehog.Internal.Range qualified as R

byteStringSizes :: [Int]
byteStringSizes = fmap (100*) [0..100]

mediumByteStrings :: H.Seed -> [BS.ByteString]
mediumByteStrings seed = makeSizedByteStrings seed byteStringSizes

bigByteStrings :: H.Seed -> [BS.ByteString]
bigByteStrings seed = makeSizedByteStrings seed (fmap (10*) byteStringSizes)
-- Up to  800,000 bytes.

--VerifySignature : check the results, maybe try with bigger inputs.


benchByteStringOneArgOp :: DefaultFun -> Benchmark
benchByteStringOneArgOp name =
    bgroup (show name) $ fmap mkBM (mediumByteStrings seedA)
           where mkBM b = benchDefault (showMemoryUsage b) $ mkApp1 name [] b


---------------- Verify signature ----------------

-- For VerifySignature, for speed purposes it shouldn't matter if the signature
-- and public key are correct as long as they're the correct sizes (256 bits/32
-- bytes for keys, 512 bytes/64 bits for signatures).
pubKey :: BS.ByteString
pubKey = genSample seedB (G.bytes (R.singleton 32))

sig :: BS.ByteString
sig = genSample seedB (G.bytes (R.singleton 64))

-- The sizes of the key and the signature are fixed (32 and 64 bytes) so we don't include
-- them in the benchmark name.  However, in models.R we still have to remove the overhead
-- for a three-argument function.
benchVerifySignature :: Benchmark
benchVerifySignature =
    bgroup (show name) $ fmap mkBM (bigByteStrings seedA)
           where name = VerifySignature
                 mkBM b = benchDefault (showMemoryUsage b) $ mkApp3 name [] pubKey b sig
-- TODO: this seems suspicious.  The benchmark results seem to be pretty much
-- constant (a few microseconds) irrespective of the size of the input, but I'm
-- pretty certain that you need to look at every byte of the input to verify the
-- signature.  If you change the size of the public key then it takes three
-- times as long, but the 'verify' implementation checks the size and fails
-- immediately if the key or signature has the wrong size.


makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks _gen =  [benchVerifySignature]
                    <> (benchByteStringOneArgOp <$> [ Sha2_256, Sha3_256, Blake2b_256 ])

-- Sha3_256 takes about 2.65 times longer than Sha2_256, which in turn takes
-- 2.82 times longer than Blake2b.  All are (very) linear in the size of the
-- input.
