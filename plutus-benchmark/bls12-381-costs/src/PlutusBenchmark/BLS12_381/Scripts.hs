-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:dump-uplc #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:simplifier-evaluate-builtins #-}

{- | Approximations of the sort of computations involving BLS12-381 primitives
 that one might wish to perform on the chain.  Real on-chain code will have
 extra overhead, but these examples help to give us an idea of the sort of
 computation that can feasibly be carried out within the validation budget
 limits.

 Some of these test vectors were produced using https://github.com/input-output-hk/bls-e2e-testvectors
 -}
module PlutusBenchmark.BLS12_381.Scripts
    ( listOfByteStringsOfLength
    , mkPairingScript
    )
where
import PlutusCore (DefaultFun, DefaultUni)
import PlutusLedgerApi.V1.Bytes qualified as P (bytes, fromHex)
import PlutusTx qualified as Tx
import PlutusTx.Plugin ()
import PlutusTx.Prelude as Tx hiding ((<>))
import UntypedPlutusCore qualified as UPLC

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as C8
import GHC.ByteOrder (ByteOrder (LittleEndian))
import Hedgehog.Internal.Gen qualified as G
import Hedgehog.Internal.Range qualified as R
import System.IO.Unsafe (unsafePerformIO)

import Prelude (fromIntegral)

-- Create a list containing n bytestrings of length l.  This could be better.
listOfByteStringsOfLength :: Integer -> Integer -> [ByteString]
listOfByteStringsOfLength n l = unsafePerformIO . G.sample $
                             G.list (R.singleton $ fromIntegral n)
                                  (G.bytes (R.singleton $ fromIntegral l))
{-# OPAQUE listOfByteStringsOfLength #-}

-- | Treat string of hexidecimal bytes literally, without encoding. Useful for hashes.
bytesFromHex :: BS.ByteString -> BuiltinByteString
bytesFromHex = toBuiltin . P.bytes . fromEither . P.fromHex
  where
    fromEither (Left _)   = traceError "bytesFromHex failed"
    fromEither (Right bs) = bs

blsSigBls12381G2XmdSha256SswuRoNul :: BuiltinByteString
blsSigBls12381G2XmdSha256SswuRoNul = toBuiltin $ C8.pack "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_NUL_"

byteString16Null :: BuiltinByteString
byteString16Null = bytesFromHex "00000000000000000000000000000000"
{-# INLINABLE byteString16Null #-}

-- Little-endian bytestring to integer conversion
byteStringToIntegerLE :: BuiltinByteString -> Integer
byteStringToIntegerLE = Tx.byteStringToInteger LittleEndian
{-# INLINABLE byteStringToIntegerLE #-}

---------------- Examples ----------------

-- Hash some bytestrings onto G1 and add them all together

-- Pairing operations

-- Take two points p1 and p2 in G1 and two points q1 and q2 in G2, apply the
-- Miller loop to (p1,q1) and (p2,q2), and then call finalVerify on the results.
runPairingFunctions
    :: BuiltinByteString  -- G1
    -> BuiltinByteString  -- G2
    -> BuiltinByteString  -- G1
    -> BuiltinByteString  -- G2
    -> Bool
runPairingFunctions _p1 _q1 p2 q2 =
    let r1 = Tx.bls12_381_millerLoop
             (Tx.bls12_381_G1_hashToGroup Tx.emptyByteString Tx.emptyByteString)
             (Tx.bls12_381_G2_hashToGroup Tx.emptyByteString Tx.emptyByteString)
        r2 = Tx.bls12_381_millerLoop (Tx.bls12_381_G1_uncompress p2) (Tx.bls12_381_G2_uncompress q2)
    in Tx.bls12_381_finalVerify r1 r2
{-# INLINABLE runPairingFunctions #-}

mkPairingScript
    :: BuiltinBLS12_381_G1_Element
    -> BuiltinBLS12_381_G2_Element
    -> BuiltinBLS12_381_G1_Element
    -> BuiltinBLS12_381_G2_Element
    -> UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkPairingScript p1 q1 p2 q2 =
    Tx.getPlcNoAnn $ $$(Tx.compile [|| runPairingFunctions ||])
          `Tx.unsafeApplyCode` (Tx.liftCodeDef $ Tx.bls12_381_G1_compress p1)
          `Tx.unsafeApplyCode` (Tx.liftCodeDef $ Tx.bls12_381_G2_compress q1)
          `Tx.unsafeApplyCode` (Tx.liftCodeDef $ Tx.bls12_381_G1_compress p2)
          `Tx.unsafeApplyCode` (Tx.liftCodeDef $ Tx.bls12_381_G2_compress q2)


