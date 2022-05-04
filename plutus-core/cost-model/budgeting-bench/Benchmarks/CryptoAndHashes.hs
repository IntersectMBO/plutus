{-# LANGUAGE OverloadedStrings #-}

module Benchmarks.CryptoAndHashes (makeBenchmarks) where

import Common
import Generators

import PlutusCore

import Criterion.Main
import Data.ByteString qualified as BS
import System.Random (StdGen)

import Hedgehog qualified as H

byteStringSizes :: [Int]
byteStringSizes = fmap (100*) [0,2..100]

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


---------------- Signature verification ----------------

-- For VerifySignature, for speed purposes it shouldn't matter if the signature
-- and public key are correct as long as they're the correct sizes (256 bits/32
-- bytes for keys, 512 bytes/64 bits for signatures).

benchVerifySignature :: Benchmark
benchVerifySignature =
    createThreeTermBuiltinBenchElementwise name [] pubkeys messages signatures
           where name = VerifySignature
                 pubkeys    = listOfSizedByteStrings 51 32
                 messages   = bigByteStrings seedA
                 signatures = listOfSizedByteStrings 51 64
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
