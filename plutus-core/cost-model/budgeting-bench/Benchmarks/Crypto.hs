-- editorconfig-checker-disable-file
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}

module Benchmarks.Crypto (makeBenchmarks) where

import Common
import Generators
import PlutusCore

import Cardano.Crypto.DSIGN.Class (ContextDSIGN, DSIGNAlgorithm, Signable, deriveVerKeyDSIGN, genKeyDSIGN,
                                   rawSerialiseSigDSIGN, rawSerialiseVerKeyDSIGN, signDSIGN)
import Cardano.Crypto.DSIGN.EcdsaSecp256k1 (EcdsaSecp256k1DSIGN, toMessageHash)
import Cardano.Crypto.DSIGN.Ed25519 (Ed25519DSIGN)
import Cardano.Crypto.DSIGN.SchnorrSecp256k1 (SchnorrSecp256k1DSIGN)
import Cardano.Crypto.Seed (mkSeedFromBytes)

import PlutusCore.BLS12_381.G1 qualified as G1
import PlutusCore.BLS12_381.G2 qualified as G2
import PlutusCore.BLS12_381.GT qualified as GT

import Criterion.Main (Benchmark, bgroup)
import Data.ByteString (ByteString)
import Hedgehog qualified as H (Seed)
import System.Random (StdGen)

numSamples :: Int
numSamples = 50

byteStringSizes :: [Int]
byteStringSizes = fmap (200*) [0..numSamples-1]

mediumByteStrings :: H.Seed -> [ByteString]
mediumByteStrings seed = makeSizedByteStrings seed byteStringSizes

bigByteStrings :: H.Seed -> [ByteString]
bigByteStrings seed = makeSizedByteStrings seed (fmap (10*) byteStringSizes)
-- Up to  784,000 bytes.


---------------- Signature verification ----------------

data MessageSize = Arbitrary | Fixed Int

{- Note [Inputs to signature verification functions] We have to use correctly
  signed messages to get worst case behaviours because some signature
  verification implementations return quickly if some basic precondition isn't
  satisfied.  For example, at least one Ed25519 signature verification
  implementation (in cardano-crypto) expects the first three bits of the final
  byte of the 64-byte signature to all be zero, and fails immediately if this is
  not the case.  This behaviour isn't documented.  Another example is that ECDSA
  verification admits two valid signatures (involving a point on a curve and its
  inverse) for a given message, but in the Bitcoin implementation for
  EcdsaSecp256k1 signatures (which we use here), only the smaller one (as a
  bytestring) is accepted.  Again, this fact isn't particularly well advertised.
  If these basic preconditions are met however, verification time should depend
  linearly on the length of the message since the whole of the message has to be
  examined before it can be determined whether a (key, message, signature)
  triple is valid or not.
-}

{- | Create a list of valid (key,message,signature) triples.  The DSIGN
   infrastructure lets us do this in a fairly generic way.  However, to sign an
   EcdsaSecp256k1DSIGN message we can't use a raw bytestring: we have to wrap it
   up using Crypto.Secp256k1.msg, which checks that the bytestring is the right
   length.  This means that we have to add a ByteString -> message conversion
   function as a parameter here.
-}
mkDsignBmInputs :: forall v msg .
    (Signable v msg, DSIGNAlgorithm v, ContextDSIGN v ~ ())
    => (ByteString -> msg)
    -> MessageSize
    -> [(ByteString, ByteString, ByteString)]
mkDsignBmInputs toMsg msgSize =
    map mkOneInput (zip seeds messages)
    where seeds = listOfSizedByteStrings numSamples 128
          -- ^ Seeds for key generation. For some algorithms the seed has to be
          -- a certain minimal size and there's a SeedBytesExhausted error if
          -- it's not big enough; 128 is big enough for everything here though.
          messages =
              case msgSize of
                Arbitrary -> bigByteStrings seedA
                Fixed n   -> listOfSizedByteStrings numSamples n
          mkOneInput (seed, msg) =
              let signKey = genKeyDSIGN @v $ mkSeedFromBytes seed                 -- Signing key (private)
                  vkBytes = rawSerialiseVerKeyDSIGN $ deriveVerKeyDSIGN signKey   -- Verification key (public)
                  sigBytes = rawSerialiseSigDSIGN $ signDSIGN () (toMsg msg) signKey
              in (vkBytes, msg, sigBytes)

benchVerifyEd25519Signature :: Benchmark
benchVerifyEd25519Signature =
    let name = VerifyEd25519Signature
        inputs = mkDsignBmInputs @Ed25519DSIGN id Arbitrary
    in createThreeTermBuiltinBenchElementwise name [] inputs

benchVerifyEcdsaSecp256k1Signature :: Benchmark
benchVerifyEcdsaSecp256k1Signature =
    let name = VerifyEcdsaSecp256k1Signature
        inputs = mkDsignBmInputs @EcdsaSecp256k1DSIGN toMsg (Fixed 32)
    in createThreeTermBuiltinBenchElementwise name [] inputs
        where toMsg b =
                  case toMessageHash b of
                    Just m  -> m
                    Nothing -> error "Invalid EcdsaSecp256k1DSIGN message"
                    -- This should only happen if we give it a message which isn't
                    -- 32 bytes long, but that shouldn't happen because of Fixed 32.

benchVerifySchnorrSecp256k1Signature :: Benchmark
benchVerifySchnorrSecp256k1Signature =
    let name = VerifySchnorrSecp256k1Signature
        inputs = mkDsignBmInputs @SchnorrSecp256k1DSIGN id Arbitrary
    in createThreeTermBuiltinBenchElementwise name [] inputs


---------------- Hashing functions ----------------

benchByteStringOneArgOp :: DefaultFun -> Benchmark
benchByteStringOneArgOp name =
    bgroup (show name) $ fmap mkBM (mediumByteStrings seedA)
           where mkBM b = benchDefault (showMemoryUsage b) $ mkApp1 name [] b


---------------- BLS12_381 buitlins ----------------


byteStrings :: [ByteString]
byteStrings = listOfSizedByteStrings 200 20

byteStringsA :: [ByteString]
byteStringsA = take 100 byteStrings

byteStringsB :: [ByteString]
byteStringsB = take 100 (drop 100 byteStrings)

g1inputsA :: [G1.Element]
g1inputsA = fmap G1.hashToCurve byteStringsA

g1inputsB :: [G1.Element]
g1inputsB = fmap G1.hashToCurve byteStringsB

g2inputsA :: [G2.Element]
g2inputsA = fmap G2.hashToCurve byteStringsA

g2inputsB :: [G2.Element]
g2inputsB = fmap G2.hashToCurve byteStringsB

-- We can only get points on G2 via millerLoop.  It should always succeed on the
-- inputs we give it here.
miller :: G1.Element -> G2.Element -> GT.Element
miller e1 e2 =
    case GT.millerLoop e1 e2 of
      Left _  -> error "millerLoop failed while generating GT points"
      Right p -> p

gtinputsA :: [GT.Element]
gtinputsA = zipWith miller g1inputsA g2inputsA

gtinputsB :: [GT.Element]
gtinputsB = zipWith miller g1inputsB g2inputsB

-- Need to generate random elements of G1 and G2, probably by hashing random
-- bytestrings to the curve.  GT is slightly problematic: we can only get points
-- on the curve by using millerLoop on elements of G1 and G2.

benchBls12_381_G1_add :: Benchmark
benchBls12_381_G1_add =
        let name = Bls12_381_G1_add
        in createTwoTermBuiltinBenchElementwise name [] g1inputsA g1inputsB
-- const
-- Two args, points on G1

benchBls12_381_G1_mul :: [Integer] -> Benchmark
benchBls12_381_G1_mul multipliers =
    let name = Bls12_381_G1_mul
    in createTwoTermBuiltinBenchElementwise name [] multipliers g1inputsA
-- linear in x (size of scalar)

benchBls12_381_G1_neg :: Benchmark
benchBls12_381_G1_neg =
    let name = Bls12_381_G1_neg
    in createOneTermBuiltinBench name [] g1inputsA
-- const

benchBls12_381_G1_equal :: Benchmark
benchBls12_381_G1_equal =
    let name = Bls12_381_G1_equal
    in createTwoTermBuiltinBenchElementwise name [] g1inputsA g1inputsA
    -- Same arguments twice
-- const

benchBls12_381_G1_hashToCurve :: Benchmark
benchBls12_381_G1_hashToCurve =
    let name = Bls12_381_G1_hashToCurve
        inputs = listOfByteStrings 100
    in createOneTermBuiltinBench name [] inputs
-- linear in input size

benchBls12_381_G1_compress :: Benchmark
benchBls12_381_G1_compress =
    let name = Bls12_381_G1_compress
    in createOneTermBuiltinBench name [] g1inputsA
-- const

benchBls12_381_G1_uncompress :: Benchmark
benchBls12_381_G1_uncompress =
    let name = Bls12_381_G1_uncompress
        inputs = fmap G1.compress g1inputsA
    in createOneTermBuiltinBench name [] inputs
-- const

benchBls12_381_G2_add :: Benchmark
benchBls12_381_G2_add =
    let name = Bls12_381_G2_add
    in createTwoTermBuiltinBenchElementwise name [] g2inputsA g2inputsB
-- const

benchBls12_381_G2_mul :: [Integer] -> Benchmark
benchBls12_381_G2_mul multipliers =
    let name = Bls12_381_G2_mul
    in createTwoTermBuiltinBenchElementwise name [] multipliers g2inputsA
-- linear in x (size of scalar)

benchBls12_381_G2_neg :: Benchmark
benchBls12_381_G2_neg =
    let name = Bls12_381_G2_neg
    in createOneTermBuiltinBench name [] g2inputsB

-- const

benchBls12_381_G2_equal :: Benchmark
benchBls12_381_G2_equal =
    let name = Bls12_381_G2_equal
    in createTwoTermBuiltinBenchElementwise name [] g2inputsA g2inputsA
    -- Same arguments twice
-- const

benchBls12_381_G2_hashToCurve :: Benchmark
benchBls12_381_G2_hashToCurve =
    let name = Bls12_381_G2_hashToCurve
        inputs = listOfByteStrings 100
    in createOneTermBuiltinBench name [] inputs
-- linear in size of input

benchBls12_381_G2_compress :: Benchmark
benchBls12_381_G2_compress =
    let name = Bls12_381_G2_compress
    in createOneTermBuiltinBench name [] g2inputsA
-- const

benchBls12_381_G2_uncompress :: Benchmark
benchBls12_381_G2_uncompress =
    let name = Bls12_381_G2_uncompress
        inputs = fmap G2.compress g2inputsA
    in createOneTermBuiltinBench name [] inputs
-- const

benchBls12_381_GT_mul :: Benchmark
benchBls12_381_GT_mul =
    let name = Bls12_381_GT_mul
    in createTwoTermBuiltinBenchElementwise name [] gtinputsA gtinputsB
-- const

benchBls12_381_GT_finalVerify :: Benchmark
benchBls12_381_GT_finalVerify =
    let name = Bls12_381_GT_finalVerify
    in createTwoTermBuiltinBenchElementwise name [] gtinputsA gtinputsB
-- const?

benchBls12_381_GT_millerLoop :: Benchmark
benchBls12_381_GT_millerLoop =
    let name = Bls12_381_GT_millerLoop
    in createTwoTermBuiltinBenchElementwise name [] g1inputsA g2inputsA
-- const?

blsBenchmarks :: StdGen -> [Benchmark]
blsBenchmarks gen =
    let multipliers = fst $ makeSizedIntegers gen [1..100] -- Constants for scalar multiplication functions
    in [ benchBls12_381_G1_add
       , benchBls12_381_G1_mul multipliers
       , benchBls12_381_G1_neg
       , benchBls12_381_G1_equal
       , benchBls12_381_G1_hashToCurve
       , benchBls12_381_G1_compress
       , benchBls12_381_G1_uncompress
       , benchBls12_381_G2_add
       , benchBls12_381_G2_mul multipliers
       , benchBls12_381_G2_neg
       , benchBls12_381_G2_equal
       , benchBls12_381_G2_hashToCurve
       , benchBls12_381_G2_compress
       , benchBls12_381_G2_uncompress
       , benchBls12_381_GT_mul
       , benchBls12_381_GT_finalVerify
       , benchBls12_381_GT_millerLoop
  ]

---------------- Main benchmarks ----------------

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen =  [ benchVerifyEd25519Signature
                      , benchVerifyEcdsaSecp256k1Signature
                      , benchVerifySchnorrSecp256k1Signature
                      ]
                     <> (benchByteStringOneArgOp <$> [Sha2_256, Sha3_256, Blake2b_256])
                     <> blsBenchmarks gen
-- Sha3_256 takes about 2.65 times longer than Sha2_256, which in turn takes
-- 2.82 times longer than Blake2b_256.  All are (very) linear in the size of the
-- input.
