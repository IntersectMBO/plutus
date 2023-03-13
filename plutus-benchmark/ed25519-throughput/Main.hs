-- editorconfig-checker-disable-file
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE NumericUnderscores  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE ViewPatterns        #-}

{- | Check how many Ed25519 signature verifications we can perform within the
   limits specified in the protocol parameters.
-}

module Main (main)

where

import PlutusCore (DefaultFun, DefaultUni)
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (exBudgetCPU, exBudgetMemory))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (..), ExMemory (..))
import PlutusTx qualified as Tx
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek

import PlutusTx.IsData (toData, unstableMakeIsData)
import PlutusTx.Prelude as Tx hiding (sort, traverse_, (*))

import Cardano.Crypto.DSIGN.Class (ContextDSIGN, DSIGNAlgorithm, Signable, deriveVerKeyDSIGN,
                                   genKeyDSIGN, rawSerialiseSigDSIGN, rawSerialiseVerKeyDSIGN,
                                   signDSIGN)
import Cardano.Crypto.DSIGN.Ed25519 (Ed25519DSIGN)
import Cardano.Crypto.Seed (mkSeedFromBytes)

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Hash qualified as Hash
import Data.Foldable (traverse_)
import Flat qualified
import Hedgehog.Internal.Gen qualified as G
import Hedgehog.Internal.Range qualified as R
import System.IO.Unsafe (unsafePerformIO)
import Text.Printf (printf)

import Prelude (Double, IO, Integral, String, fromIntegral, (*), (/))

-- Protocol parameters (November 2022)

-- | This is the "maximum transaction size".  We're just comparing the size of
-- the script with this, so our results may be a little optimistic if the
-- transaction includes other stuff (I'm not sure exactly what "maximum
-- transaction size" means).
max_tx_size :: Integer
max_tx_size = 16384

max_tx_ex_steps :: Integer
max_tx_ex_steps = 10_000_000_000

max_tx_ex_mem :: Integer
max_tx_ex_mem = 14_000_000


-------------------------------- PLC stuff--------------------------------

type UTerm   = UPLC.Term    UPLC.NamedDeBruijn DefaultUni DefaultFun ()
type UProg   = UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
type UDBProg = UPLC.Program UPLC.DeBruijn      DefaultUni DefaultFun ()


compiledCodeToTerm
    :: Tx.CompiledCodeIn DefaultUni DefaultFun a -> UTerm
compiledCodeToTerm (Tx.getPlcNoAnn -> UPLC.Program _ _ body) = body

{- | Remove the textual names from a NamedDeBruijn program -}
toAnonDeBruijnProg :: UProg -> UDBProg
toAnonDeBruijnProg (UPLC.Program () ver body) =
    UPLC.Program () ver $ UPLC.termMapNames (\(UPLC.NamedDeBruijn _ ix) -> UPLC.DeBruijn ix) body


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
mkSigCheckScript :: Integer -> UProg
mkSigCheckScript n =
    Tx.getPlcNoAnn $ $$(Tx.compile [|| verifyInputs builtinHash ||]) `Tx.unsafeApplyCode` Tx.liftCode (mkInputsAsData n haskellHash)

-- Printing utilities
percentage :: (Integral a, Integral b) => a -> b -> Double
percentage a b =
    let a' = fromIntegral a :: Double
        b' = fromIntegral b :: Double
    in (a'/b' * 100)

percentTxt :: (Integral a, Integral b) => a -> b -> String
percentTxt a b = printf "(%.1f%%)" (percentage a b)

-- | Evaluate a script and return the CPU and memory costs (according to the cost model)
evaluate :: UProg -> (Integer, Integer)
evaluate (UPLC.Program _ _ prog) =
    case Cek.runCekDeBruijn PLC.defaultCekParameters Cek.tallying Cek.noEmitter prog of
      (_res, Cek.TallyingSt _ budget, _logs) ->
          let ExCPU cpu = exBudgetCPU budget
              ExMemory mem = exBudgetMemory budget
          in (fromIntegral cpu, fromIntegral mem)

-- | Evaluate a script and print out the serialised size and the CPU and memory
-- usage, both as absolute values and percentages of the maxima specified in the
-- protocol parameters.
printStatistics :: Integer -> IO ()
printStatistics n = do
    let script = mkSigCheckScript n
        serialised = Flat.flat (toAnonDeBruijnProg script)
        size = BS.length serialised
        (cpu, mem) = evaluate script
    printf "  %3d %7d %8s %15d %8s %15d %8s \n"
           n
           size (percentTxt size max_tx_size)
           cpu  (percentTxt cpu  max_tx_ex_steps)
           mem  (percentTxt mem  max_tx_ex_mem)

-- | Check that the Haskell version succeeds on a list of inputs.
testHaskell :: Integer -> IO ()
testHaskell n =
    if verifyInputs builtinHash $ mkInputsAsData n haskellHash
    then printf "Off-chain version succeeded on %d inputs\n\n" n
    else printf "Off-chain version failed\n\n"

main :: IO ()
main = do
  testHaskell 100
  printf "    n     script size             CPU usage               Memory usage\n"
  printf "  ----------------------------------------------------------------------\n"
  traverse_ printStatistics [0, 10..150]
