-- editorconfig-checker-disable-file
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module Benchmarks.Crypto (makeBenchmarks) where

import Common
import Generators
import PlutusBenchmark.Common (EvaluationContext)

import PlutusCore

import Cardano.Crypto.DSIGN.Class (ContextDSIGN, DSIGNAlgorithm, Signable, deriveVerKeyDSIGN,
                                   genKeyDSIGN, rawSerialiseSigDSIGN, rawSerialiseVerKeyDSIGN,
                                   signDSIGN)
import Cardano.Crypto.DSIGN.EcdsaSecp256k1 (EcdsaSecp256k1DSIGN, toMessageHash)
import Cardano.Crypto.DSIGN.Ed25519 (Ed25519DSIGN)
import Cardano.Crypto.DSIGN.SchnorrSecp256k1 (SchnorrSecp256k1DSIGN)
import Cardano.Crypto.Seed (mkSeedFromBytes)

import PlutusCore.Crypto.BLS12_381.G1 qualified as G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as Pairing

import Criterion.Main (Benchmark, bgroup)
import Data.ByteString (ByteString, empty)
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
    where seeds = listOfByteStringsOfLength numSamples 128
          -- ^ Seeds for key generation. For some algorithms the seed has to be
          -- a certain minimal size and there's a SeedBytesExhausted error if
          -- it's not big enough; 128 is big enough for everything here though.
          messages =
              case msgSize of
                Arbitrary -> bigByteStrings seedA
                Fixed n   -> listOfByteStringsOfLength numSamples n
          mkOneInput (seed, msg) =
              let signKey = genKeyDSIGN @v $ mkSeedFromBytes seed                 -- Signing key (private)
                  vkBytes = rawSerialiseVerKeyDSIGN $ deriveVerKeyDSIGN signKey   -- Verification key (public)
                  sigBytes = rawSerialiseSigDSIGN $ signDSIGN () (toMsg msg) signKey
              in (vkBytes, msg, sigBytes)

benchVerifyEd25519Signature :: EvaluationContext -> Benchmark
benchVerifyEd25519Signature evalCtx =
    let name = VerifyEd25519Signature
        inputs = mkDsignBmInputs @Ed25519DSIGN id Arbitrary
    in createThreeTermBuiltinBenchElementwise evalCtx name [] inputs

benchVerifyEcdsaSecp256k1Signature :: EvaluationContext -> Benchmark
benchVerifyEcdsaSecp256k1Signature evalCtx =
    let name = VerifyEcdsaSecp256k1Signature
        inputs = mkDsignBmInputs @EcdsaSecp256k1DSIGN toMsg (Fixed 32)
    in createThreeTermBuiltinBenchElementwise evalCtx name [] inputs
        where toMsg b =
                  case toMessageHash b of
                    Just m  -> m
                    Nothing -> error "Invalid EcdsaSecp256k1DSIGN message"
                    -- This should only happen if we give it a message which isn't
                    -- 32 bytes long, but that shouldn't happen because of Fixed 32.

benchVerifySchnorrSecp256k1Signature :: EvaluationContext -> Benchmark
benchVerifySchnorrSecp256k1Signature evalCtx =
    let name = VerifySchnorrSecp256k1Signature
        inputs = mkDsignBmInputs @SchnorrSecp256k1DSIGN id Arbitrary
    in createThreeTermBuiltinBenchElementwise evalCtx name [] inputs


---------------- Hashing functions ----------------

benchByteStringOneArgOp :: EvaluationContext -> DefaultFun -> Benchmark
benchByteStringOneArgOp evalCtx name =
    bgroup (show name) $ fmap mkBM (mediumByteStrings seedA)
           where mkBM b = benchWithCtx evalCtx (showMemoryUsage b) $ mkApp1 name [] b


---------------- BLS12_381 buitlins ----------------


byteStrings :: [ByteString]
byteStrings = listOfByteStringsOfLength 200 20

byteStringsA :: [ByteString]
byteStringsA = take 100 byteStrings

byteStringsB :: [ByteString]
byteStringsB = take 100 (drop 100 byteStrings)


-- Random elements in G1

-- Create random group elements by hashing a random bytestring (with an empty
-- DST). This will always give us a valid group element, unlike uncompressing
-- random bytestrings, which will almost always fail.
randomG1Element :: ByteString -> G1.Element
randomG1Element s =
    case G1.hashToGroup s Data.ByteString.empty of
      Left err -> error $ "Error in randomG1Element: " ++ show err
      Right p  -> p

g1inputsA :: [G1.Element]
g1inputsA = fmap randomG1Element byteStringsA

g1inputsB :: [G1.Element]
g1inputsB = fmap randomG1Element byteStringsB

-- Random elements in G2
randomG2Element :: ByteString -> G2.Element
randomG2Element s =
    case G2.hashToGroup s Data.ByteString.empty of
      Left err -> error $ "Error in randomG2Element: " ++ show err
      Right p  -> p

g2inputsA :: [G2.Element]
g2inputsA = fmap randomG2Element byteStringsA

g2inputsB :: [G2.Element]
g2inputsB = fmap randomG2Element byteStringsB

-- Random values of type MlResult.  The only way we can manufacture values of
-- this type is by using millerLoop, which should always succeed on the inputs
-- we give it here.
gtinputsA :: [Pairing.MlResult]
gtinputsA = zipWith Pairing.millerLoop g1inputsA g2inputsA

gtinputsB :: [Pairing.MlResult]
gtinputsB = zipWith Pairing.millerLoop g1inputsB g2inputsB

benchBls12_381_G1_add :: EvaluationContext -> Benchmark
benchBls12_381_G1_add evalCtx =
  let name = Bls12_381_G1_add
  in createTwoTermBuiltinBenchElementwise evalCtx name [] $ zip g1inputsA g1inputsB
  -- constant time
  -- Two arguments, points on G1

benchBls12_381_G1_neg :: EvaluationContext -> Benchmark
benchBls12_381_G1_neg evalCtx =
  let name = Bls12_381_G1_neg
  in createOneTermBuiltinBench evalCtx name [] g1inputsA
  -- constant time

benchBls12_381_G1_scalarMul :: EvaluationContext -> [Integer] -> Benchmark
benchBls12_381_G1_scalarMul evalCtx multipliers =
  let name = Bls12_381_G1_scalarMul
  in createTwoTermBuiltinBenchElementwise evalCtx name [] $ zip multipliers g1inputsA
  -- linear in x (size of scalar)

benchBls12_381_G1_equal :: EvaluationContext -> Benchmark
benchBls12_381_G1_equal evalCtx =
  let name = Bls12_381_G1_equal
  in createTwoTermBuiltinBenchElementwise evalCtx name [] $ zip g1inputsA g1inputsA
  -- Same arguments twice
  -- constant time

benchBls12_381_G1_hashToGroup :: EvaluationContext -> Benchmark
benchBls12_381_G1_hashToGroup evalCtx =
  let name = Bls12_381_G1_hashToGroup
      inputs = listOfByteStrings 100
      -- The maximum length of a DST is 255 bytes, so let's use that for all
      -- cases (DST size shouldn't make much difference anyway).
      dsts = listOfByteStringsOfLength 100 255
  in createTwoTermBuiltinBenchElementwise evalCtx name [] $ zip inputs dsts
  -- linear in input size

benchBls12_381_G1_compress :: EvaluationContext -> Benchmark
benchBls12_381_G1_compress evalCtx =
  let name = Bls12_381_G1_compress
  in createOneTermBuiltinBench evalCtx name [] g1inputsA
  -- constant time

benchBls12_381_G1_uncompress :: EvaluationContext -> Benchmark
benchBls12_381_G1_uncompress evalCtx =
  let name = Bls12_381_G1_uncompress
      inputs = fmap G1.compress g1inputsA
  in createOneTermBuiltinBench evalCtx name [] inputs
  -- constant time

benchBls12_381_G2_add :: EvaluationContext -> Benchmark
benchBls12_381_G2_add evalCtx =
  let name = Bls12_381_G2_add
  in createTwoTermBuiltinBenchElementwise evalCtx name [] $ zip g2inputsA g2inputsB
  -- constant time

benchBls12_381_G2_neg :: EvaluationContext -> Benchmark
benchBls12_381_G2_neg evalCtx =
  let name = Bls12_381_G2_neg
  in createOneTermBuiltinBench evalCtx name [] g2inputsB
  -- constant time

benchBls12_381_G2_scalarMul :: EvaluationContext -> [Integer] -> Benchmark
benchBls12_381_G2_scalarMul evalCtx multipliers =
  let name = Bls12_381_G2_scalarMul
  in createTwoTermBuiltinBenchElementwise evalCtx name [] $ zip multipliers g2inputsA
  -- linear in x (size of scalar)

benchBls12_381_G2_equal :: EvaluationContext -> Benchmark
benchBls12_381_G2_equal evalCtx =
  let name = Bls12_381_G2_equal
  in createTwoTermBuiltinBenchElementwise evalCtx name [] $ zip g2inputsA g2inputsA
  -- Same arguments twice
  -- constant time

benchBls12_381_G2_hashToGroup :: EvaluationContext -> Benchmark
benchBls12_381_G2_hashToGroup evalCtx =
  let name = Bls12_381_G2_hashToGroup
      inputs = listOfByteStrings 100
      dsts = listOfByteStringsOfLength 100 255
  in createTwoTermBuiltinBenchElementwise evalCtx name [] $ zip inputs dsts
  -- linear in size of input

benchBls12_381_G2_compress :: EvaluationContext -> Benchmark
benchBls12_381_G2_compress evalCtx =
  let name = Bls12_381_G2_compress
  in createOneTermBuiltinBench evalCtx name [] g2inputsA
  -- constant time

benchBls12_381_G2_uncompress :: EvaluationContext -> Benchmark
benchBls12_381_G2_uncompress evalCtx =
  let name = Bls12_381_G2_uncompress
      inputs = fmap G2.compress g2inputsA
  in createOneTermBuiltinBench evalCtx name [] inputs
  -- constant time

benchBls12_381_millerLoop :: EvaluationContext -> Benchmark
benchBls12_381_millerLoop evalCtx =
  let name = Bls12_381_millerLoop
  in createTwoTermBuiltinBenchElementwise evalCtx name [] $ zip g1inputsA g2inputsA
  -- constant time

benchBls12_381_mulMlResult :: EvaluationContext -> Benchmark
benchBls12_381_mulMlResult evalCtx =
  let name = Bls12_381_mulMlResult
  in createTwoTermBuiltinBenchElementwise evalCtx name [] $ zip gtinputsA gtinputsB
  -- constant time

benchBls12_381_finalVerify :: EvaluationContext -> Benchmark
benchBls12_381_finalVerify evalCtx =
  let name = Bls12_381_finalVerify
  in createTwoTermBuiltinBenchElementwise evalCtx name [] $ zip gtinputsA gtinputsB
  -- constant time


blsBenchmarks :: EvaluationContext -> StdGen -> [Benchmark]
blsBenchmarks evalCtx gen =
    let multipliers = fst $ makeSizedIntegers gen [1..100] -- Constants for scalar multiplication functions
    in [ benchBls12_381_G1_add         evalCtx
       , benchBls12_381_G1_neg         evalCtx
       , benchBls12_381_G1_scalarMul   evalCtx multipliers
       , benchBls12_381_G1_equal       evalCtx
       , benchBls12_381_G1_hashToGroup evalCtx
       , benchBls12_381_G1_compress    evalCtx
       , benchBls12_381_G1_uncompress  evalCtx
       , benchBls12_381_G2_add         evalCtx
       , benchBls12_381_G2_neg         evalCtx
       , benchBls12_381_G2_scalarMul   evalCtx multipliers
       , benchBls12_381_G2_equal       evalCtx
       , benchBls12_381_G2_hashToGroup evalCtx
       , benchBls12_381_G2_compress    evalCtx
       , benchBls12_381_G2_uncompress  evalCtx
       , benchBls12_381_millerLoop     evalCtx
       , benchBls12_381_mulMlResult    evalCtx
       , benchBls12_381_finalVerify    evalCtx
     ]

---------------- Main benchmarks ----------------

makeBenchmarks :: EvaluationContext -> StdGen -> [Benchmark]
makeBenchmarks evalCtx gen =
  [ benchVerifyEd25519Signature evalCtx
  , benchVerifyEcdsaSecp256k1Signature evalCtx
  , benchVerifySchnorrSecp256k1Signature evalCtx
  ]
  <> (benchByteStringOneArgOp evalCtx <$> [Sha2_256, Sha3_256, Blake2b_224, Blake2b_256, Keccak_256, Ripemd_160])
  <> blsBenchmarks evalCtx gen
