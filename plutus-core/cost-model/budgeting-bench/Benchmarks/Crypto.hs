{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}

-- | Budgeting benchmarks for cryptographic functions, including hashing.
module Benchmarks.Crypto (makeBenchmarks) where

import Common
import Generators
import PlutusCore

import Cardano.Crypto.DSIGN.Class
import Cardano.Crypto.DSIGN.EcdsaSecp256k1 (EcdsaSecp256k1DSIGN, toMessageHash)
import Cardano.Crypto.DSIGN.Ed25519 (Ed25519DSIGN)
import Cardano.Crypto.DSIGN.SchnorrSecp256k1 (SchnorrSecp256k1DSIGN)
import Cardano.Crypto.Seed (mkSeedFromBytes)

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
mkBmInputs :: forall v msg .
    (Signable v msg, DSIGNAlgorithm v, ContextDSIGN v ~ ())
    => (ByteString -> msg)
    -> MessageSize
    -> [(ByteString, ByteString, ByteString)]
mkBmInputs toMsg msgSize =
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
                  -- Signing key (private)
              let signKey = genKeyDSIGN @v $ mkSeedFromBytes seed
                  -- Verification key (public)
                  vkBytes = rawSerialiseVerKeyDSIGN $ deriveVerKeyDSIGN signKey
                  sigBytes = rawSerialiseSigDSIGN $ signDSIGN () (toMsg msg) signKey
              in (vkBytes, msg, sigBytes)

benchVerifyEd25519Signature :: Benchmark
benchVerifyEd25519Signature =
    let name = VerifyEd25519Signature
        inputs = mkBmInputs @Ed25519DSIGN id Arbitrary
    in createThreeTermBuiltinBenchElementwise name [] inputs

benchVerifyEcdsaSecp256k1Signature :: Benchmark
benchVerifyEcdsaSecp256k1Signature =
    let name = VerifyEcdsaSecp256k1Signature
        inputs = mkBmInputs @EcdsaSecp256k1DSIGN toMsg (Fixed 32)
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
        inputs = mkBmInputs @SchnorrSecp256k1DSIGN id Arbitrary
    in createThreeTermBuiltinBenchElementwise name [] inputs


---------------- Hashing functions ----------------

benchByteStringOneArgOp :: DefaultFun -> Benchmark
benchByteStringOneArgOp name =
    bgroup (show name) $ fmap mkBM (mediumByteStrings seedA)
           where mkBM b = benchDefault (showMemoryUsage b) $ mkApp1 name [] b


---------------- Main benchmarks ----------------

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks _gen =
    [benchVerifyEd25519Signature
    , benchVerifyEcdsaSecp256k1Signature
    , benchVerifySchnorrSecp256k1Signature]
        <> (benchByteStringOneArgOp <$> [Sha2_256, Sha3_256, Blake2b_256])

-- Sha3_256 takes about 2.65 times longer than Sha2_256, which in turn takes
-- 2.82 times longer than Blake2b_256.  All are (very) linear in the size of the
-- input.
