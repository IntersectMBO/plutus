{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}

module Benchmarks.CryptoAndHashes (makeBenchmarks) where

import Common
import Generators
import PlutusCore

import Cardano.Crypto.DSIGN.Class (ContextDSIGN, DSIGNAlgorithm, SignKeyDSIGN, Signable, deriveVerKeyDSIGN, genKeyDSIGN,
                                   rawDeserialiseSigDSIGN, rawDeserialiseVerKeyDSIGN, rawSerialiseSigDSIGN,
                                   rawSerialiseVerKeyDSIGN, signDSIGN)
import Cardano.Crypto.DSIGN.EcdsaSecp256k1 (EcdsaSecp256k1DSIGN, SigDSIGN, VerKeyDSIGN)
import Cardano.Crypto.DSIGN.Ed25519 (Ed25519DSIGN)
import Cardano.Crypto.DSIGN.SchnorrSecp256k1 (SchnorrSecp256k1DSIGN)
import Cardano.Crypto.Seed (mkSeedFromBytes)

import Criterion.Main
import Crypto.Secp256k1 qualified (msg)
import Data.ByteString (ByteString)
import Hedgehog qualified as H
import System.Random (StdGen)

numSamples :: Int
numSamples = 5

byteStringSizes :: [Int]
byteStringSizes = fmap (200*) [0..numSamples-1]

mediumByteStrings :: H.Seed -> [ByteString]
mediumByteStrings seed = makeSizedByteStrings seed byteStringSizes

bigByteStrings :: H.Seed -> [ByteString]
bigByteStrings seed = makeSizedByteStrings seed (fmap (10*) byteStringSizes)
-- Up to  784,000 bytes.

data MessageSize = Arbitrary | Fixed Int

mkBmInputs :: forall v msg .
    (Signable v msg, DSIGNAlgorithm v, ContextDSIGN v ~ ())
    => (ByteString -> Maybe msg)
    -> MessageSize
    -> [(ByteString, ByteString, ByteString)]
mkBmInputs toMsg msgSize =
    map mkOneInput (zip seeds messages)
    where seeds = listOfSizedByteStrings numSamples 128
          -- For some algortihms the seed has to be a certain minimal size, and
          -- there's a SeedBytesExhausted error if it's not big enough; 128
          -- seems to be OK for everything here.
          messages =
              case msgSize of
                Arbitrary -> bigByteStrings seedA
                Fixed n   -> listOfSizedByteStrings numSamples n
          getMsg x = case toMsg x of { Nothing -> error "Invalid message";  Just m -> m }
          mkOneInput (seed, msg) =
              let signKey = genKeyDSIGN @v $ mkSeedFromBytes seed
                  sigBytes = rawSerialiseSigDSIGN $ signDSIGN () (getMsg msg) signKey
                  vkBytes = rawSerialiseVerKeyDSIGN $ deriveVerKeyDSIGN signKey
              in (vkBytes, msg, sigBytes)

mkBmInputs' :: forall v msg .
    (Signable v msg, DSIGNAlgorithm v, ContextDSIGN v ~ ())
    => MessageSize
    -> (ByteString, ByteString, ByteString)
mkBmInputs' msgSize =
    mkOneInput seed message
    where seed = head $ listOfSizedByteStrings numSamples 128
          -- For some algortihms the seed has to be a certain minimal size, and
          -- there's a SeedBytesExhausted error if it's not big enough; 128
          -- seems to be OK for everything here.
          message =
              case msgSize of
                Arbitrary -> head $ bigByteStrings seedA
                Fixed n   -> head $ listOfSizedByteStrings numSamples n
          mkOneInput seed msg =
              let signKey = genKeyDSIGN @EcdsaSecp256k1DSIGN $ mkSeedFromBytes seed
                  sigBytes = rawSerialiseSigDSIGN $ signDSIGN () (fromJust $ Crypto.Secp256k1.msg msg) signKey
                  vkBytes = rawSerialiseVerKeyDSIGN $ deriveVerKeyDSIGN signKey
              in (vkBytes, msg, sigBytes)
          fromJust (Just x) = x
          fromJust Nothing  = error "Nothing"
-- Why do we have to explicitly convert bytestrings to messages for Secp256k1?
-- We didn't have to do that before.

---------------- Signature verification ----------------

-- Signature verification functions.  Wrong input sizes cause error, time should
-- be otherwise independent of correctness/incorrectness of signature.

-- For VerifyEd25519Signature, for speed purposes it shouldn't matter if the
-- signature and public key are correct as long as they're the correct sizes
-- (256 bits/32 bytes for keys, 512 bytes/64 bits for signatures).

benchVerifyEd25519Signature :: Benchmark
benchVerifyEd25519Signature =
    let name = VerifyEd25519Signature
        inputs = mkBmInputs @Ed25519DSIGN Just Arbitrary
    in createThreeTermBuiltinBenchElementwise name [] inputs

benchVerifyEcdsaSecp256k1Signature :: Benchmark
benchVerifyEcdsaSecp256k1Signature =
    let name = VerifyEcdsaSecp256k1Signature
        inputs = mkBmInputs @EcdsaSecp256k1DSIGN Crypto.Secp256k1.msg (Fixed 32)
    in createThreeTermBuiltinBenchElementwise name [] inputs

benchVerifySchnorrSecp256k1Signature :: Benchmark
benchVerifySchnorrSecp256k1Signature =
    let name = VerifySchnorrSecp256k1Signature
        inputs = mkBmInputs @SchnorrSecp256k1DSIGN Just Arbitrary
    in createThreeTermBuiltinBenchElementwise name [] inputs


--- Old benchmarks

benchVerifyEd25519SignatureX :: Benchmark
benchVerifyEd25519SignatureX =
    createThreeTermBuiltinBenchElementwise name [] $ zip3 pubkeys messages signatures
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

benchVerifyEcdsaSecp256k1SignatureX :: Benchmark
benchVerifyEcdsaSecp256k1SignatureX =
    createThreeTermBuiltinBenchElementwise name [] $ zip3 pubkeys messages signatures
        where name = VerifyEcdsaSecp256k1Signature
              pubkeys    = listOfSizedByteStrings 50 64
              messages   = listOfSizedByteStrings 50 32
              signatures = listOfSizedByteStrings 50 64
-- NB: verifyEcdsaSecp256k1Signature returns immediately for 50% of
-- randomly-chosen signatures: see Note [ECDSA secp256k1 signature verification]
-- in Builtins.hs.  This doesn't apply to VerifySchnorrSecp256k1Signature.


benchVerifySchnorrSecp256k1SignatureX :: Benchmark
benchVerifySchnorrSecp256k1SignatureX =
    createThreeTermBuiltinBenchElementwise name [] $ zip3 pubkeys messages signatures
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
