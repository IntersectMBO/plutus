-- editorconfig-checker-disable-file
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}

{- | Check how many Ed25519 signature verifications we can perform within the
   limits specified in the protocol parameters.
-}

module PlutusBenchmark.Ed25519.Common (runTests)
where

import PlutusBenchmark.Common

import System.IO (Handle)

import PlutusCore (DefaultFun, DefaultUni)
import PlutusCore.Crypto.Hash qualified as Hash
import PlutusTx qualified as Tx
import UntypedPlutusCore qualified as UPLC

import PlutusTx.IsData (toData, unstableMakeIsData)
import PlutusTx.Prelude as Tx hiding (sort, (*))

import Cardano.Crypto.DSIGN.Class (ContextDSIGN, DSIGNAlgorithm, Signable, deriveVerKeyDSIGN,
                                   genKeyDSIGN, rawSerialiseSigDSIGN, rawSerialiseVerKeyDSIGN,
                                   signDSIGN)
import Cardano.Crypto.DSIGN.Ed25519 (Ed25519DSIGN)
import Cardano.Crypto.Seed (mkSeedFromBytes)

import Data.ByteString (ByteString)
import Hedgehog.Internal.Gen qualified as G
import Hedgehog.Internal.Range qualified as R
import System.IO.Unsafe (unsafePerformIO)
import Text.Printf (hPrintf)

import Prelude (IO, fromIntegral, mapM_, (*))

---------------- Inputs ----------------

{- | Generate n public keys P_1,...,P_n (we'll call these the "data keys") and
   hash them to get n hashes H_1,...,H_n.  Sign all of the hashes with different
   private keys K_1,...,K_n (with corresponding public keys V_1,...V_n) to get n
   signatures S_1,...,S_n.  We create a list of (V_i, H_i, S_i, P_i) tuples,
   convert it to Data, and feed that to a script which

     1. Verifies each (V_i, H_i, S_i) to check that the signatures are valid.
     2. Hashes each P_i to make sure that it matches H_i.

   This program does that for varying values of n and prints statistics about
   the size, cpu cost, and memory cost of the script.
-}


data Inputs = Inputs [(BuiltinByteString, BuiltinByteString, BuiltinByteString, BuiltinByteString)]
type HashFun = ByteString -> ByteString
type BuiltinHashFun = BuiltinByteString -> BuiltinByteString

unstableMakeIsData ''Inputs

haskellHash :: HashFun
haskellHash = Hash.sha2_256

{-# INLINEABLE builtinHash #-}
builtinHash :: BuiltinHashFun
builtinHash = Tx.sha2_256

-- Create a list containing n bytestrings of length l.  This could be better.
{-# NOINLINE listOfSizedByteStrings #-}
listOfSizedByteStrings :: Integer -> Integer -> [ByteString]
listOfSizedByteStrings n l = unsafePerformIO . G.sample $
                             G.list (R.singleton $ fromIntegral n)
                                  (G.bytes (R.singleton $ fromIntegral l))

{- | Create a list of valid (verification key, message, signature, data key)
   quadruples.  The DSIGN infrastructure lets us do this in a fairly generic
   way.  However, to sign an EcdsaSecp256k1DSIGN message we can't use a raw
   bytestring: we have to wrap it up using Crypto.Secp256k1.msg, which checks
   that the bytestring is the right length.  This means that we have to add a
   ByteString -> message conversion function as a parameter here.  The full
   generality isn't need here, but let's leave it in anyway.
-}
mkInputs :: forall v msg .
    (Signable v msg, DSIGNAlgorithm v, ContextDSIGN v ~ ())
    => Integer
    -> (ByteString -> msg)
    -> HashFun
    -> Inputs
mkInputs n toMsg hash =
    Inputs $ map mkOneInput (zip seeds1 seeds2)
    where seedSize = 128
          (seeds1, seeds2) = splitAt n $ listOfSizedByteStrings (2*n) seedSize
          -- ^ Seeds for key generation. For some algorithms the seed has to be
          -- a certain minimal size and there's a SeedBytesExhausted error if
          -- it's not big enough; 128 is big enough for everything here though.
          mkOneInput (seed1, seed2) =
              let signKey1    = genKeyDSIGN @v $ mkSeedFromBytes seed1
                  dataKey     = rawSerialiseVerKeyDSIGN $ deriveVerKeyDSIGN signKey1   -- public key to be checked
                  dataKeyHash = hash dataKey :: ByteString
                  signKey2    = genKeyDSIGN @v $ mkSeedFromBytes seed2                 -- Signing key (private)
                  vkBytes     = rawSerialiseVerKeyDSIGN $ deriveVerKeyDSIGN signKey2   -- Verification key (public)
                  sigBytes    = rawSerialiseSigDSIGN $ signDSIGN () (toMsg dataKeyHash) signKey2
              in (toBuiltin vkBytes, toBuiltin sigBytes, toBuiltin dataKeyHash, toBuiltin dataKey)

mkInputsAsData :: Integer -> HashFun -> BuiltinData
mkInputsAsData n hash = Tx.dataToBuiltinData $ toData (mkInputs @Ed25519DSIGN n id hash)

-- | Check conditions (1) and (2) mentioned above.  We check these for all of
-- the inputs and return True if everything succeeds and False if there's at
-- least one failure.  We're being a little careful with the computation of the
-- arguments to the two occurrences of && in this function to defeat the
-- short-circuiting and make sure that the amount of computation is the same
-- whether verification succeeds or fails.  If the inputs are generated
-- correctly (which is checked by testHaskell when we run `main`) then
-- verification always succeeds, but let's be careful just in case.
{-# INLINEABLE verifyInputs #-}
verifyInputs :: BuiltinHashFun -> BuiltinData -> Bool
verifyInputs hash d =
    case Tx.fromBuiltinData d of
      Nothing              -> Tx.error ()
      Just (Inputs inputs) -> verify inputs True
          where verify [] acc     = acc
                verify (i:is) acc = verify is (checkInput i && acc) -- checkInput first
                checkInput (vk, sg, dkhash, dk) =
                    let dkhash' = hash dk
                        hashesEq = dkhash == dkhash'
                    in Tx.verifyEd25519Signature vk dkhash sg && hashesEq

-- | Create the input data, convert it to BuiltinData, and apply the
-- verification script to that.
mkSigCheckScript :: Integer -> UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkSigCheckScript n =
    Tx.getPlcNoAnn $ $$(Tx.compile [|| verifyInputs builtinHash ||]) `Tx.unsafeApplyCode` Tx.liftCodeDef (mkInputsAsData n haskellHash)

printSigCheckCosts :: Handle -> Integer -> IO ()
printSigCheckCosts h n = printSizeStatistics h (TestSize n) (mkSigCheckScript n)

-- | Check that the Haskell version succeeds on a list of inputs.
testHaskell :: Handle -> Integer -> IO ()
testHaskell h n =
    if verifyInputs builtinHash $ mkInputsAsData n haskellHash
    then hPrintf h "Off-chain version succeeded on %d inputs\n" n
    else hPrintf h "Off-chain version failed\n"

runTests :: Handle -> IO ()
runTests h = do
  printHeader h
  mapM_ (printSigCheckCosts h) [0, 10..150]
  hPrintf h "\n"
  testHaskell h 100
