module Benchmarks.CryptoAndHashes (makeBenchmarks) where

import Common
import Generators

import PlutusCore

import Criterion.Main
import Data.ByteString qualified as BS
import System.Random (StdGen)

import Hedgehog qualified as H

byteStringSizes :: [Int]
byteStringSizes = fmap (100*) [0,2..98]

mediumByteStrings :: H.Seed -> [BS.ByteString]
mediumByteStrings seed = makeSizedByteStrings seed byteStringSizes

bigByteStrings :: H.Seed -> [BS.ByteString]
bigByteStrings seed = makeSizedByteStrings seed (fmap (10*) byteStringSizes)
-- Up to  784,000 bytes.


---------------- Signature verification ----------------

-- Signature verification functions.  Wrong input sizes cause error, time should
-- be otherwise independent of correctness/incorrectness of signature.

-- For VerifyEd25519Signature, for speed purposes it shouldn't matter if the
-- signature and public key are correct as long as they're the correct sizes
-- (256 bits/32 bytes for keys, 512 bytes/64 bits for signatures).

benchVerifyEd25519Signature :: Benchmark
benchVerifyEd25519Signature =
    createThreeTermBuiltinBenchElementwise name [] pubkeys messages signatures
           where name = VerifyEd25519Signature
                 pubkeys    = listOfSizedByteStrings 50 32
                 messages   = bigByteStrings seedA
                 signatures = listOfSizedByteStrings 50 64
-- TODO: this seems suspicious.  The benchmark results seem to be pretty much
-- constant (a few microseconds) irrespective of the size of the input, but I'm
-- pretty certain that you need to look at every byte of the input to verify the
-- signature.  If you change the size of the public key then it takes three
-- times as long, but the 'verify' implementation checks the size and fails
-- immediately if the key or signature has the wrong size. [This is possibly due
-- to the fact that the underlying C implementation is *extremely* fast, but
-- there's quite a bit of error handling when an argument is the wrong size.
-- However in the latter case the program will terminate anyway, so we don't
-- care about costing it accurately.] Just to be sure, check the results, maybe
-- try with bigger inputs.

benchVerifyEcdsaSecp256k1Signature :: Benchmark
benchVerifyEcdsaSecp256k1Signature =
    createThreeTermBuiltinBenchElementwise name [] pubkeys messages signatures
        where name = VerifyEcdsaSecp256k1Signature
              pubkeys    = listOfSizedByteStrings 50 64
              messages   = listOfSizedByteStrings 50 32
              signatures = listOfSizedByteStrings 50 64
-- NB: verifyEcdsaSecp256k1Signature returns immediately for 50% of
-- randomly-chosen signatures: see Note [ECDSA secp256k1 signature verification]
-- in Builtins.hs.  This doesn't apply to VerifySchnorrSecp256k1Signature.


benchVerifySchnorrSecp256k1Signature :: Benchmark
benchVerifySchnorrSecp256k1Signature =
    createThreeTermBuiltinBenchElementwise name [] pubkeys messages signatures
        where name = VerifySchnorrSecp256k1Signature
              pubkeys    = listOfSizedByteStrings 50 64
              messages   = bigByteStrings seedA
              signatures = listOfSizedByteStrings 50 64


---------------- Hashing functions ----------------

benchByteStringOneArgOp :: DefaultFun -> Benchmark
benchByteStringOneArgOp name =
    bgroup (show name) $ fmap mkBM (mediumByteStrings seedA)
           where mkBM b = benchDefault (showMemoryUsage b) $ mkApp1 name [] b


---------------- Main benchmarks ----------------

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks _gen =  [benchVerifyEd25519Signature, benchVerifyEcdsaSecp256k1Signature, benchVerifySchnorrSecp256k1Signature]
                       <> (benchByteStringOneArgOp <$> [Sha2_256, Sha3_256, Blake2b_256])

-- Sha3_256 takes about 2.65 times longer than Sha2_256, which in turn takes
-- 2.82 times longer than Blake2b_256.  All are (very) linear in the size of the
-- input.
