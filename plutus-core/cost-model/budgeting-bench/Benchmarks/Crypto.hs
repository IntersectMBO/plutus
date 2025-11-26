-- editorconfig-checker-disable-file
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Benchmarks.Crypto (makeBenchmarks) where

import Common
import Generators
import PlutusCore

import Cardano.Crypto.DSIGN.Class
  ( ContextDSIGN
  , DSIGNAlgorithm
  , Signable
  , deriveVerKeyDSIGN
  , genKeyDSIGN
  , rawSerialiseSigDSIGN
  , rawSerialiseVerKeyDSIGN
  , signDSIGN
  )
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
byteStringSizes = fmap (200 *) [0 .. numSamples - 1]

mediumByteStrings :: H.Seed -> [ByteString]
mediumByteStrings seed = makeSizedByteStrings seed byteStringSizes

bigByteStrings :: H.Seed -> [ByteString]
bigByteStrings seed = makeSizedByteStrings seed (fmap (10 *) byteStringSizes)

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

{-| Create a list of valid (key,message,signature) triples.  The DSIGN
   infrastructure lets us do this in a fairly generic way.  However, to sign an
   EcdsaSecp256k1DSIGN message we can't use a raw bytestring: we have to wrap it
   up using Crypto.Secp256k1.msg, which checks that the bytestring is the right
   length.  This means that we have to add a ByteString -> message conversion
   function as a parameter here. -}
mkDsignBmInputs
  :: forall v msg
   . (Signable v msg, DSIGNAlgorithm v, ContextDSIGN v ~ ())
  => (ByteString -> msg)
  -> MessageSize
  -> [(ByteString, ByteString, ByteString)]
mkDsignBmInputs toMsg msgSize =
  map mkOneInput (zip seeds messages)
  where
    seeds = listOfByteStringsOfLength numSamples 128
    -- \^ Seeds for key generation. For some algorithms the seed has to be
    -- a certain minimal size and there's a SeedBytesExhausted error if
    -- it's not big enough; 128 is big enough for everything here though.
    messages =
      case msgSize of
        Arbitrary -> bigByteStrings seedA
        Fixed n -> listOfByteStringsOfLength numSamples n
    mkOneInput (seed, msg) =
      let signKey = genKeyDSIGN @v $ mkSeedFromBytes seed -- Signing key (private)
          vkBytes = rawSerialiseVerKeyDSIGN $ deriveVerKeyDSIGN signKey -- Verification key (public)
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
  where
    toMsg b =
      case toMessageHash b of
        Just m -> m
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
  where
    mkBM b = benchDefault (showMemoryUsage b) $ mkApp1 name [] b

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
    Right p -> p

g1inputsA :: [G1.Element]
g1inputsA = fmap randomG1Element byteStringsA

g1inputsB :: [G1.Element]
g1inputsB = fmap randomG1Element byteStringsB

-- Random elements in G2
randomG2Element :: ByteString -> G2.Element
randomG2Element s =
  case G2.hashToGroup s Data.ByteString.empty of
    Left err -> error $ "Error in randomG2Element: " ++ show err
    Right p -> p

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

benchBls12_381_G1_add :: Benchmark
benchBls12_381_G1_add =
  let name = Bls12_381_G1_add
   in createTwoTermBuiltinBenchElementwise name [] $ zip g1inputsA g1inputsB

-- constant time
-- Two arguments, points on G1

benchBls12_381_G1_neg :: Benchmark
benchBls12_381_G1_neg =
  let name = Bls12_381_G1_neg
   in createOneTermBuiltinBench name [] g1inputsA

-- constant time

benchBls12_381_G1_scalarMul :: [Integer] -> Benchmark
benchBls12_381_G1_scalarMul multipliers =
  let name = Bls12_381_G1_scalarMul
   in createTwoTermBuiltinBenchElementwise name [] $ zip multipliers g1inputsA

-- linear in x (size of scalar)

benchBls12_381_G1_multiScalarMul :: [[Integer]] -> Benchmark
benchBls12_381_G1_multiScalarMul scalarLists =
  let name = Bls12_381_G1_multiScalarMul
      g1Lists = [fmap randomG1Element (listOfByteStringsOfLength (length scalars) 20) | scalars <- scalarLists]
   in createTwoTermBuiltinBenchElementwise name [] (zip scalarLists g1Lists)

-- linear in size of the minimum of both lists

benchBls12_381_G1_equal :: Benchmark
benchBls12_381_G1_equal =
  let name = Bls12_381_G1_equal
   in createTwoTermBuiltinBenchElementwise name [] $ zip g1inputsA g1inputsA

-- Same arguments twice
-- constant time

benchBls12_381_G1_hashToGroup :: Benchmark
benchBls12_381_G1_hashToGroup =
  let name = Bls12_381_G1_hashToGroup
      inputs = listOfByteStrings 100
      -- The maximum length of a DST is 255 bytes, so let's use that for all
      -- cases (DST size shouldn't make much difference anyway).
      dsts = listOfByteStringsOfLength 100 255
   in createTwoTermBuiltinBenchElementwise name [] $ zip inputs dsts

-- linear in input size

benchBls12_381_G1_compress :: Benchmark
benchBls12_381_G1_compress =
  let name = Bls12_381_G1_compress
   in createOneTermBuiltinBench name [] g1inputsA

-- constant time

benchBls12_381_G1_uncompress :: Benchmark
benchBls12_381_G1_uncompress =
  let name = Bls12_381_G1_uncompress
      inputs = fmap G1.compress g1inputsA
   in createOneTermBuiltinBench name [] inputs

-- constant time

benchBls12_381_G2_add :: Benchmark
benchBls12_381_G2_add =
  let name = Bls12_381_G2_add
   in createTwoTermBuiltinBenchElementwise name [] $ zip g2inputsA g2inputsB

-- constant time

benchBls12_381_G2_neg :: Benchmark
benchBls12_381_G2_neg =
  let name = Bls12_381_G2_neg
   in createOneTermBuiltinBench name [] g2inputsB

-- constant time

benchBls12_381_G2_scalarMul :: [Integer] -> Benchmark
benchBls12_381_G2_scalarMul multipliers =
  let name = Bls12_381_G2_scalarMul
   in createTwoTermBuiltinBenchElementwise name [] $ zip multipliers g2inputsA

-- linear in x (size of scalar)

benchBls12_381_G2_multiScalarMul :: [[Integer]] -> Benchmark
benchBls12_381_G2_multiScalarMul scalarLists =
  let name = Bls12_381_G2_multiScalarMul
      g2Lists = [fmap randomG2Element (listOfByteStringsOfLength (length scalars) 20) | scalars <- scalarLists]
   in createTwoTermBuiltinBenchElementwise name [] (zip scalarLists g2Lists)

-- linear in size of the minimum of both lists

benchBls12_381_G2_equal :: Benchmark
benchBls12_381_G2_equal =
  let name = Bls12_381_G2_equal
   in createTwoTermBuiltinBenchElementwise name [] $ zip g2inputsA g2inputsA

-- Same arguments twice
-- constant time

benchBls12_381_G2_hashToGroup :: Benchmark
benchBls12_381_G2_hashToGroup =
  let name = Bls12_381_G2_hashToGroup
      inputs = listOfByteStrings 100
      dsts = listOfByteStringsOfLength 100 255
   in createTwoTermBuiltinBenchElementwise name [] $ zip inputs dsts

-- linear in size of input

benchBls12_381_G2_compress :: Benchmark
benchBls12_381_G2_compress =
  let name = Bls12_381_G2_compress
   in createOneTermBuiltinBench name [] g2inputsA

-- constant time

benchBls12_381_G2_uncompress :: Benchmark
benchBls12_381_G2_uncompress =
  let name = Bls12_381_G2_uncompress
      inputs = fmap G2.compress g2inputsA
   in createOneTermBuiltinBench name [] inputs

-- constant time

benchBls12_381_millerLoop :: Benchmark
benchBls12_381_millerLoop =
  let name = Bls12_381_millerLoop
   in createTwoTermBuiltinBenchElementwise name [] $ zip g1inputsA g2inputsA

-- constant time

benchBls12_381_mulMlResult :: Benchmark
benchBls12_381_mulMlResult =
  let name = Bls12_381_mulMlResult
   in createTwoTermBuiltinBenchElementwise name [] $ zip gtinputsA gtinputsB

-- constant time

benchBls12_381_finalVerify :: Benchmark
benchBls12_381_finalVerify =
  let name = Bls12_381_finalVerify
   in createTwoTermBuiltinBenchElementwise name [] $ zip gtinputsA gtinputsB

-- constant time

-- A helper function to generate lists of integers of a given sizes
mkVariableLengthScalarLists :: StdGen -> [Int] -> ([[Integer]], StdGen)
mkVariableLengthScalarLists gen = foldl go ([], gen)
  where
    go (acc, g) size =
      let (ints, g') = makeSizedIntegers g [1 .. size]
       in (acc ++ [ints], g')

blsBenchmarks :: StdGen -> [Benchmark]
blsBenchmarks gen =
  let multipliers = fst $ makeSizedIntegers gen [1 .. 100] -- Constants for scalar multiplication functions
      scalarLists = fst $ mkVariableLengthScalarLists gen [1 .. 100] -- Create a list of lists of integers of various sizes between 1 and 100 elements
   in [ benchBls12_381_G1_add
      , benchBls12_381_G1_neg
      , benchBls12_381_G1_scalarMul multipliers
      , benchBls12_381_G1_multiScalarMul scalarLists
      , benchBls12_381_G1_equal
      , benchBls12_381_G1_hashToGroup
      , benchBls12_381_G1_compress
      , benchBls12_381_G1_uncompress
      , benchBls12_381_G2_add
      , benchBls12_381_G2_neg
      , benchBls12_381_G2_scalarMul multipliers
      , benchBls12_381_G2_multiScalarMul scalarLists
      , benchBls12_381_G2_equal
      , benchBls12_381_G2_hashToGroup
      , benchBls12_381_G2_compress
      , benchBls12_381_G2_uncompress
      , benchBls12_381_millerLoop
      , benchBls12_381_mulMlResult
      , benchBls12_381_finalVerify
      ]

---------------- Main benchmarks ----------------

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen =
  [ benchVerifyEd25519Signature
  , benchVerifyEcdsaSecp256k1Signature
  , benchVerifySchnorrSecp256k1Signature
  ]
    <> (benchByteStringOneArgOp <$> [Sha2_256, Sha3_256, Blake2b_224, Blake2b_256, Keccak_256, Ripemd_160])
    <> blsBenchmarks gen
