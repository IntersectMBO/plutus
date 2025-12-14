-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}

{-| Approximations of the sort of computations involving BLS12-381 primitives
 that one might wish to perform on the chain.  Real on-chain code will have
 extra overhead, but these examples help to give us an idea of the sort of
 computation that can feasibly be carried out within the validation budget
 limits.

 Some of these test vectors were produced using https://github.com/input-output-hk/bls-e2e-testvectors -}
module PlutusBenchmark.BLS12_381.Scripts
  ( checkGroth16Verify_Haskell
  , listOfByteStringsOfLength
  , mkGroth16VerifyScript
  , mkHashAndAddG1Script
  , mkHashAndAddG2Script
  , mkPairingScript
  , mkUncompressAndAddG1Script
  , mkUncompressAndAddG2Script
  , mkVerifyBlsSimplePolicy
  , checkVerifyBlsSimpleScript
  , mkVrfBlsPolicy
  , checkVrfBlsScript
  , mkG1VerifyPolicy
  , checkG1VerifyScript
  , mkG2VerifyPolicy
  , checkG2VerifyScript
  , mkAggregateSingleKeyG1Policy
  , checkAggregateSingleKeyG1Script
  , mkAggregateMultiKeyG2Policy
  , checkAggregateMultiKeyG2Script
  , mkSchnorrG1VerifyPolicy
  , checkSchnorrG1VerifyScript
  , mkSchnorrG2VerifyPolicy
  , checkSchnorrG2VerifyScript
  )
where

import PlutusCore (DefaultFun, DefaultUni)
import PlutusLedgerApi.V1.Bytes qualified as P (bytes, fromHex)
import PlutusTx qualified as Tx
import PlutusTx.List qualified as List
import PlutusTx.Plugin ()
import PlutusTx.Prelude as Tx hiding ((<>))
import UntypedPlutusCore qualified as UPLC

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as C8
import Data.Semigroup ((<>))
import GHC.ByteOrder (ByteOrder (LittleEndian))
import Hedgehog.Internal.Gen qualified as G
import Hedgehog.Internal.Range qualified as R
import System.IO.Unsafe (unsafePerformIO)

import Prelude (fromIntegral)

-- Create a list containing n bytestrings of length l.  This could be better.
listOfByteStringsOfLength :: Integer -> Integer -> [ByteString]
listOfByteStringsOfLength n l =
  unsafePerformIO
    . G.sample
    $ G.list
      (R.singleton $ fromIntegral n)
      (G.bytes (R.singleton $ fromIntegral l))
{-# OPAQUE listOfByteStringsOfLength #-}

-- | Treat string of hexidecimal bytes literally, without encoding. Useful for hashes.
bytesFromHex :: BS.ByteString -> BuiltinByteString
bytesFromHex = toBuiltin . P.bytes . fromEither . P.fromHex
  where
    fromEither (Left _) = traceError "bytesFromHex failed"
    fromEither (Right bs) = bs

blsSigBls12381G2XmdSha256SswuRoNul :: BuiltinByteString
blsSigBls12381G2XmdSha256SswuRoNul = toBuiltin $ C8.pack "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_NUL_"

byteString16Null :: BuiltinByteString
byteString16Null = bytesFromHex "00000000000000000000000000000000"
{-# INLINEABLE byteString16Null #-}

-- Little-endian bytestring to integer conversion
byteStringToIntegerLE :: BuiltinByteString -> Integer
byteStringToIntegerLE = Tx.byteStringToInteger LittleEndian
{-# INLINEABLE byteStringToIntegerLE #-}

---------------- Examples ----------------

-- Hash some bytestrings onto G1 and add them all together

hashAndAddG1 :: [BuiltinByteString] -> BuiltinBLS12_381_G1_Element
hashAndAddG1 l =
  go l (Tx.bls12_381_G1_uncompress Tx.bls12_381_G1_compressed_zero)
  where
    go [] !acc = acc
    go (q : qs) !acc = go qs $ Tx.bls12_381_G1_add (Tx.bls12_381_G1_hashToGroup q emptyByteString) acc
{-# INLINEABLE hashAndAddG1 #-}

mkHashAndAddG1Script :: [ByteString] -> UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkHashAndAddG1Script l =
  let points = List.map toBuiltin l
   in Tx.getPlcNoAnn $ $$(Tx.compile [||hashAndAddG1||]) `Tx.unsafeApplyCode` Tx.liftCodeDef points

-- Hash some bytestrings onto G2 and add them all together
hashAndAddG2 :: [BuiltinByteString] -> BuiltinBLS12_381_G2_Element
hashAndAddG2 l =
  go l (Tx.bls12_381_G2_uncompress Tx.bls12_381_G2_compressed_zero)
  where
    go [] !acc = acc
    go (q : qs) !acc = go qs $ Tx.bls12_381_G2_add (Tx.bls12_381_G2_hashToGroup q emptyByteString) acc
{-# INLINEABLE hashAndAddG2 #-}

mkHashAndAddG2Script :: [ByteString] -> UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkHashAndAddG2Script l =
  let points = List.map toBuiltin l
   in Tx.getPlcNoAnn $ $$(Tx.compile [||hashAndAddG2||]) `Tx.unsafeApplyCode` Tx.liftCodeDef points

-- Uncompress a list of compressed G1 points and add them all together
uncompressAndAddG1 :: [BuiltinByteString] -> BuiltinBLS12_381_G1_Element
uncompressAndAddG1 l =
  go l (Tx.bls12_381_G1_uncompress Tx.bls12_381_G1_compressed_zero)
  where
    go [] acc = acc
    go (q : qs) acc = go qs $ Tx.bls12_381_G1_add (Tx.bls12_381_G1_uncompress q) acc
{-# INLINEABLE uncompressAndAddG1 #-}

mkUncompressAndAddG1Script :: [ByteString] -> UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkUncompressAndAddG1Script l =
  let ramdomPoint bs = Tx.bls12_381_G1_hashToGroup bs emptyByteString
      points = List.map (Tx.bls12_381_G1_compress . ramdomPoint . toBuiltin) l
   in Tx.getPlcNoAnn $ $$(Tx.compile [||uncompressAndAddG1||]) `Tx.unsafeApplyCode` Tx.liftCodeDef points

-- Uncompress a list of compressed G1 points and add them all together
uncompressAndAddG2 :: [BuiltinByteString] -> BuiltinBLS12_381_G2_Element
uncompressAndAddG2 l =
  go l (Tx.bls12_381_G2_uncompress Tx.bls12_381_G2_compressed_zero)
  where
    go [] acc = acc
    go (q : qs) acc = go qs $ Tx.bls12_381_G2_add (Tx.bls12_381_G2_uncompress q) acc
{-# INLINEABLE uncompressAndAddG2 #-}

mkUncompressAndAddG2Script :: [ByteString] -> UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkUncompressAndAddG2Script l =
  let ramdomPoint bs = Tx.bls12_381_G2_hashToGroup bs emptyByteString
      points = List.map (Tx.bls12_381_G2_compress . ramdomPoint . toBuiltin) l
   in Tx.getPlcNoAnn $ $$(Tx.compile [||uncompressAndAddG2||]) `Tx.unsafeApplyCode` Tx.liftCodeDef points

-- Pairing operations

-- Take two points p1 and p2 in G1 and two points q1 and q2 in G2, apply the
-- Miller loop to (p1,q1) and (p2,q2), and then call finalVerify on the results.
runPairingFunctions
  :: BuiltinByteString -- G1
  -> BuiltinByteString -- G2
  -> BuiltinByteString -- G1
  -> BuiltinByteString -- G2
  -> Bool
runPairingFunctions p1 q1 p2 q2 =
  let r1 = Tx.bls12_381_millerLoop (Tx.bls12_381_G1_uncompress p1) (Tx.bls12_381_G2_uncompress q1)
      r2 = Tx.bls12_381_millerLoop (Tx.bls12_381_G1_uncompress p2) (Tx.bls12_381_G2_uncompress q2)
   in Tx.bls12_381_finalVerify r1 r2
{-# INLINEABLE runPairingFunctions #-}

mkPairingScript
  :: BuiltinBLS12_381_G1_Element
  -> BuiltinBLS12_381_G2_Element
  -> BuiltinBLS12_381_G1_Element
  -> BuiltinBLS12_381_G2_Element
  -> UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkPairingScript p1 q1 p2 q2 =
  Tx.getPlcNoAnn
    $ $$(Tx.compile [||runPairingFunctions||])
    `Tx.unsafeApplyCode` (Tx.liftCodeDef $ Tx.bls12_381_G1_compress p1)
    `Tx.unsafeApplyCode` (Tx.liftCodeDef $ Tx.bls12_381_G2_compress q1)
    `Tx.unsafeApplyCode` (Tx.liftCodeDef $ Tx.bls12_381_G1_compress p2)
    `Tx.unsafeApplyCode` (Tx.liftCodeDef $ Tx.bls12_381_G2_compress q2)

---------------- Groth16 verification ----------------

{-| An example of the on-chain computation required for verification of a Groth16
 proof.  The data here is derived from
 https://github.com/achimcc/groth16-example/blob/main/src/lib.rs -}

-- Wrappers for compressed group elements for slightly better type safety
newtype CompressedG1Element = CompressedG1Element {g1 :: BuiltinByteString}
  deriving newtype (Tx.Lift DefaultUni)

mkG1Element :: ByteString -> CompressedG1Element
mkG1Element = CompressedG1Element . bytesFromHex

newtype CompressedG2Element = CompressedG2Element {g2 :: BuiltinByteString}
  deriving newtype (Tx.Lift DefaultUni)

mkG2Element :: ByteString -> CompressedG2Element
mkG2Element = CompressedG2Element . bytesFromHex

groth16scalar :: Integer
groth16scalar = 0x1884d0cbcc5947434e46d19b3e904e18a8ee8d0d39ce9d315f3b00e338c8f618

-- Lots of group elements for input to the computation

groth16alpha :: CompressedG1Element
groth16alpha =
  mkG1Element
    ( "b71db1fa5f41362e93025b3556d76ead1225cf590d1cdb9e"
        <> "382a1febb7963dcd24a51e18df04ab221becaf29169faf25"
    )

groth16beta :: CompressedG2Element
groth16beta =
  mkG2Element
    ( "b3a26b0b4712e78d5d71786d96132a7c585023a36632cada"
        <> "44171ac3f45db524c3f6570c8a3f7dec35ae1ac3309b05dd"
        <> "0b306db4f74fd9ec421ca70c54425d922eac4c403b00db91"
        <> "6fdedf065bdce00ece17b97a4e97173e4d5989818edfaa4c"
    )

groth16gamma :: CompressedG2Element
groth16gamma =
  mkG2Element
    ( "b5acb800cd49ed8cbddbf491a1fcf8abfc93f09d38bbb2ec"
        <> "b6b08e23a4642ce59c9b0386539ac3cecdfb66a9f027fc21"
        <> "0f259510756444bc5eef654f4d0612b5d6375f9526b1b966"
        <> "ce53b8f12594e1b399d08231cfe6c269a44aa8d587f2369d"
    )

groth16delta :: CompressedG2Element
groth16delta =
  mkG2Element
    ( "b3aa797bafa39a48f6f87c2483c894c281c807821c47301f"
        <> "fb755acfcfd22c2323cedf6349c7fedd3200a4ae558631e5"
        <> "01d299eb93135c07cf694ca118d1b386490529c60f57935c"
        <> "efa89fcafa13a83f84207b76fe078dc859d402743d468c15"
    )

groth16gamma_abc_1 :: CompressedG1Element
groth16gamma_abc_1 =
  mkG1Element
    ( "b7f6d06dd3e5246ef6b51b075c30b68fd490fbf85e0205f7"
        <> "9fa04d81133192139463b5e8efb22c39ef3dd1c5092015b8"
    )

groth16gamma_abc_2 :: CompressedG1Element
groth16gamma_abc_2 =
  mkG1Element
    ( "a2e637dbff52a1e4a8c5d985b3411fc5fd44af607e42923e"
        <> "abb47ad876e1f02b5be034adaf73952ae8affee5f51841de"
    )

groth16a :: CompressedG1Element
groth16a =
  mkG1Element
    ( "a05be50fab5795bb8784393a5045f98747173ad287f55e21"
        <> "3471bd559745551452453c4c3a39e7c88310849f3c7a1fc3"
    )

groth16b :: CompressedG2Element
groth16b =
  mkG2Element
    ( "ad6348b6b7b34c86bf37a748cd2d82a250dfc64846756688"
        <> "25a16f7da6a04d3424113e325ce734ec44956082c0a06e5f"
        <> "1868e1f1a6e559b9fe81f1a901f8a6341b301c45b25d3080"
        <> "fbc5039353d8f71b550b274ec4c07c70cd1153562c314c97"
    )

groth16c :: CompressedG1Element
groth16c =
  mkG1Element
    ( "b569cc491b4df035cbf49e951fd4fe30aa8236b0e2af68f4"
        <> "c1592cd40debeb718af33639db6bc1e2da9d98e553e5eaed"
    )

groth16Verify
  :: BuiltinByteString -- G1
  -> BuiltinByteString -- G2
  -> BuiltinByteString -- G2
  -> BuiltinByteString -- G2
  -> BuiltinByteString -- G1
  -> BuiltinByteString -- G1
  -> BuiltinByteString -- G1
  -> BuiltinByteString -- G2
  -> BuiltinByteString -- G1
  -> Integer
  -> Bool
groth16Verify
  (Tx.bls12_381_G1_uncompress -> alpha)
  (Tx.bls12_381_G2_uncompress -> beta)
  (Tx.bls12_381_G2_uncompress -> gamma)
  (Tx.bls12_381_G2_uncompress -> delta)
  (Tx.bls12_381_G1_uncompress -> abc1)
  (Tx.bls12_381_G1_uncompress -> abc2)
  (Tx.bls12_381_G1_uncompress -> a)
  (Tx.bls12_381_G2_uncompress -> b)
  (Tx.bls12_381_G1_uncompress -> c)
  s =
    let l1 = Tx.bls12_381_millerLoop a b
        l2 = Tx.bls12_381_millerLoop alpha beta
        l3 = Tx.bls12_381_millerLoop c delta
        p = Tx.bls12_381_G1_add abc1 (Tx.bls12_381_G1_scalarMul s abc2)
        l4 = Tx.bls12_381_millerLoop p gamma
        y = Tx.bls12_381_mulMlResult l2 (Tx.bls12_381_mulMlResult l3 l4)
     in Tx.bls12_381_finalVerify l1 y
{-# INLINEABLE groth16Verify #-}

{-| Make a UPLC script applying groth16Verify to the inputs.  Passing the
 newtype inputs increases the size and CPU cost slightly, so we unwrap them
 first.  This should return `True`. -}
mkGroth16VerifyScript :: UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkGroth16VerifyScript =
  Tx.getPlcNoAnn
    $ $$(Tx.compile [||groth16Verify||])
    `Tx.unsafeApplyCode` (Tx.liftCodeDef $ g1 groth16alpha)
    `Tx.unsafeApplyCode` (Tx.liftCodeDef $ g2 groth16beta)
    `Tx.unsafeApplyCode` (Tx.liftCodeDef $ g2 groth16gamma)
    `Tx.unsafeApplyCode` (Tx.liftCodeDef $ g2 groth16delta)
    `Tx.unsafeApplyCode` (Tx.liftCodeDef $ g1 groth16gamma_abc_1)
    `Tx.unsafeApplyCode` (Tx.liftCodeDef $ g1 groth16gamma_abc_2)
    `Tx.unsafeApplyCode` (Tx.liftCodeDef $ g1 groth16a)
    `Tx.unsafeApplyCode` (Tx.liftCodeDef $ g2 groth16b)
    `Tx.unsafeApplyCode` (Tx.liftCodeDef $ g1 groth16c)
    `Tx.unsafeApplyCode` Tx.liftCodeDef groth16scalar

-- | Check that the Haskell version returns the correct result.
checkGroth16Verify_Haskell :: Bool
checkGroth16Verify_Haskell =
  groth16Verify
    (g1 groth16alpha)
    (g2 groth16beta)
    (g2 groth16gamma)
    (g2 groth16delta)
    (g1 groth16gamma_abc_1)
    (g1 groth16gamma_abc_2)
    (g1 groth16a)
    (g2 groth16b)
    (g1 groth16c)
    groth16scalar

---------------- Simple Sign and Verify ----------------

simpleVerifyPrivKey :: Integer
simpleVerifyPrivKey = 50166937291276222007610100461546392414157570314060957244808461481762532157524
{-# INLINEABLE simpleVerifyPrivKey #-}

simpleVerifyMessage :: BuiltinByteString
simpleVerifyMessage = "I am a message"
{-# INLINEABLE simpleVerifyMessage #-}

verifyBlsSimpleScript :: Integer -> BuiltinByteString -> Bool
verifyBlsSimpleScript privKey message =
  let g1generator = Tx.bls12_381_G1_uncompress Tx.bls12_381_G1_compressed_generator

      -- calculate public key
      pubKey = Tx.bls12_381_G1_scalarMul privKey g1generator

      -- Hash this msg to the G2
      msgToG2 = Tx.bls12_381_G2_hashToGroup message Tx.emptyByteString

      -- Create signature artifact in G2 with private key
      sigma = Tx.bls12_381_G2_scalarMul privKey msgToG2
   in -- verify the msg with signature sigma with the check e(g1,sigma)=e(pub,msgToG2)
      Tx.bls12_381_finalVerify (Tx.bls12_381_millerLoop g1generator sigma) (Tx.bls12_381_millerLoop pubKey msgToG2)
{-# INLINEABLE verifyBlsSimpleScript #-}

checkVerifyBlsSimpleScript :: Bool
checkVerifyBlsSimpleScript = verifyBlsSimpleScript simpleVerifyPrivKey simpleVerifyMessage

mkVerifyBlsSimplePolicy :: UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkVerifyBlsSimplePolicy =
  Tx.getPlcNoAnn
    $ $$(Tx.compile [||verifyBlsSimpleScript||])
    `Tx.unsafeApplyCode` Tx.liftCodeDef simpleVerifyPrivKey
    `Tx.unsafeApplyCode` Tx.liftCodeDef simpleVerifyMessage

---------------- VRF ----------------

{- A basic VRF using G2 (note G1 is cheaper)
   For reference see https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-15#name-elliptic-curve-vrf-ecvrf)
   and more readable and mathematical in nature see https://eprint.iacr.org/2017/099.pdf.
-}

vrfPrivKey :: Integer
vrfPrivKey = 50166937291276222007610100461546392414157570314060957244808461481762532157524 :: Integer
{-# INLINEABLE vrfPrivKey #-}

vrfMessage :: BuiltinByteString
vrfMessage = "I am a message" :: BuiltinByteString
{-# INLINEABLE vrfMessage #-}

data VrfProof = VrfProof
  { vrfProofGamma :: BuiltinByteString
  , vrfProofC :: BuiltinByteString
  , vrfProofS :: Integer
  }
Tx.makeLift ''VrfProof
Tx.unstableMakeIsData ''VrfProof

data VrfProofWithOutput = VrfProofWithOutput
  { vrfProofOutput :: BuiltinByteString
  , vrfProofProof :: VrfProof
  }
Tx.makeLift ''VrfProofWithOutput
Tx.unstableMakeIsData ''VrfProofWithOutput

vrfBlsScript :: BuiltinByteString -> BuiltinByteString -> VrfProofWithOutput -> Bool
vrfBlsScript message pubKey (VrfProofWithOutput beta (VrfProof gamma c s)) =
  let
    -- cofactor of G2
    f = 305502333931268344200999753193121504214466019254188142667664032982267604182971884026507427359259977847832272839041692990889188039904403802465579155252111 :: Integer

    -- The proof of that the VRF hash of input alpha under our priv key is beta
    -- To verify a VRF hash given an
    --        input alpha
    --        output beta
    --        proof pi (gamma, c, s)
    --        pubkey pub
    -- do the following calculation
    pubKey' = Tx.bls12_381_G2_uncompress pubKey
    g2generator = Tx.bls12_381_G2_uncompress bls12_381_G2_compressed_generator
    u = Tx.bls12_381_G2_add (Tx.bls12_381_G2_scalarMul (byteStringToIntegerLE c) pubKey') (Tx.bls12_381_G2_scalarMul s g2generator)
    h = Tx.bls12_381_G2_hashToGroup message emptyByteString
    v = Tx.bls12_381_G2_add (Tx.bls12_381_G2_scalarMul (byteStringToIntegerLE c) (Tx.bls12_381_G2_uncompress gamma)) (Tx.bls12_381_G2_scalarMul s h)
   in
    -- and check

    c
      == (sha2_256 . mconcat $ Tx.bls12_381_G2_compress <$> [g2generator, h, pubKey', Tx.bls12_381_G2_uncompress gamma, u, v])
      && beta
      == (sha2_256 . Tx.bls12_381_G2_compress $ Tx.bls12_381_G2_scalarMul f (Tx.bls12_381_G2_uncompress gamma))
{-# INLINEABLE vrfBlsScript #-}

-- used offchain to generate the vrf proof output
generateVrfProof :: Integer -> BuiltinByteString -> VrfProofWithOutput
generateVrfProof privKey message =
  let g2generator = Tx.bls12_381_G2_uncompress bls12_381_G2_compressed_generator

      -- calculate public key
      pub = Tx.bls12_381_G2_scalarMul privKey g2generator

      -- hash this msg to G2
      h = Tx.bls12_381_G2_hashToGroup message emptyByteString

      -- define first element of the proof of correct VRF
      gamma = Tx.bls12_381_G2_scalarMul privKey h
      -- gammaComp = Tx.bls12_381_G2_compress gamma

      -- for this signed hash with preimage alpha, define a ephemeral interger (for each signature take a new one)
      -- Random 32 byte int
      k = 108204667002115086588596846168569722098834602153875763359385781912495445631691 :: Integer

      -- define second element of the proof of correct VRF
      -- the paper notes that this can actually be truncated to 128 bits without loss of the 128 bits security.
      -- truncating this will allow for smaller proof sizes.
      c =
        sha2_256
          . mconcat
          $ Tx.bls12_381_G2_compress
          <$> [g2generator, h, pub, gamma, Tx.bls12_381_G2_scalarMul k g2generator, Tx.bls12_381_G2_scalarMul k h]

      -- define the third and last element of a proof of correct VRF
      s = (k - (byteStringToIntegerLE c) * privKey) `modulo` 52435875175126190479447740508185965837690552500527637822603658699938581184513

      -- cofactor of G2
      f = 305502333931268344200999753193121504214466019254188142667664032982267604182971884026507427359259977847832272839041692990889188039904403802465579155252111 :: Integer

      -- create our VRF hash output
      beta = sha2_256 . Tx.bls12_381_G2_compress $ Tx.bls12_381_G2_scalarMul f gamma
   in VrfProofWithOutput beta (VrfProof (Tx.bls12_381_G2_compress gamma) c s)

checkVrfBlsScript :: Bool
checkVrfBlsScript =
  let g2generator = Tx.bls12_381_G2_uncompress Tx.bls12_381_G2_compressed_generator
      pk = Tx.bls12_381_G2_compress $ Tx.bls12_381_G2_scalarMul vrfPrivKey g2generator
   in vrfBlsScript vrfMessage pk (generateVrfProof vrfPrivKey vrfMessage)

mkVrfBlsPolicy :: UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkVrfBlsPolicy =
  let g2generator = Tx.bls12_381_G2_uncompress Tx.bls12_381_G2_compressed_generator
   in Tx.getPlcNoAnn
        $ $$(Tx.compile [||vrfBlsScript||])
        `Tx.unsafeApplyCode` Tx.liftCodeDef vrfMessage
        `Tx.unsafeApplyCode` Tx.liftCodeDef (Tx.bls12_381_G2_compress $ Tx.bls12_381_G2_scalarMul vrfPrivKey g2generator)
        `Tx.unsafeApplyCode` Tx.liftCodeDef (generateVrfProof vrfPrivKey vrfMessage)

---------------- Verify over G1 ----------------

{- BLS signature with the public key over G1. This function returns a message `msg`, a public
   key `pk`, and a signature `sig`. Verification of these test vectors should proceed as follows:
    * pk_deser = G1Decompress(pk)
    * sig_deser = G2Decompress(sig)
    * hashed_msg = G2HashToCurve(msg, "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_NUL_")
    * Check that pairing(pk_deser, hashed_msg) = pairing(G1Generator, sig_deser)
-}

g1VerifyMessage :: BuiltinByteString
g1VerifyMessage = bytesFromHex "3e00ef2f895f40d67f5bb8e81f09a5a12c840ec3ce9a7f3b181be188ef711a1e"
{-# INLINEABLE g1VerifyMessage #-}

g1VerifyPubKey :: BuiltinByteString
g1VerifyPubKey =
  bytesFromHex
    ( "aa04a34d4db073e41505ebb84eee16c0094fde9fa22ec974"
        <> "adb36e5b3df5b2608639f091bff99b5f090b3608c3990173"
    )
{-# INLINEABLE g1VerifyPubKey #-}

g1VerifySignature :: BuiltinByteString
g1VerifySignature =
  bytesFromHex
    ( "808ccec5435a63ae01e10d81be2707ab55cd0dfc235dfdf9f70ad32799e42510d67c9f61d98a6578a96a76cf6f4c105d"
        <> "09262ec1d86b06515360b290e7d52d347e48438de2ea2233f3c72a0c2221ed2da5e115367bca7a2712165032340e0b29"
    )
{-# INLINEABLE g1VerifySignature #-}

g1VerifyScript
  :: BuiltinByteString
  -> BuiltinByteString
  -> BuiltinByteString
  -> BuiltinByteString
  -> Bool
g1VerifyScript message pubKey signature dst =
  let g1generator = Tx.bls12_381_G1_uncompress Tx.bls12_381_G1_compressed_generator
      pkDeser = Tx.bls12_381_G1_uncompress pubKey
      sigDeser = Tx.bls12_381_G2_uncompress signature
      hashedMsg = Tx.bls12_381_G2_hashToGroup message dst
   in Tx.bls12_381_finalVerify
        (Tx.bls12_381_millerLoop pkDeser hashedMsg)
        (Tx.bls12_381_millerLoop g1generator sigDeser)
{-# INLINEABLE g1VerifyScript #-}

checkG1VerifyScript :: Bool
checkG1VerifyScript = g1VerifyScript g1VerifyMessage g1VerifyPubKey g1VerifySignature blsSigBls12381G2XmdSha256SswuRoNul

mkG1VerifyPolicy :: UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkG1VerifyPolicy =
  Tx.getPlcNoAnn
    $ $$(Tx.compile [||g1VerifyScript||])
    `Tx.unsafeApplyCode` Tx.liftCodeDef g1VerifyMessage
    `Tx.unsafeApplyCode` Tx.liftCodeDef g1VerifyPubKey
    `Tx.unsafeApplyCode` Tx.liftCodeDef g1VerifySignature
    `Tx.unsafeApplyCode` Tx.liftCodeDef blsSigBls12381G2XmdSha256SswuRoNul

---------------- Verify over G2 ----------------

{- BLS signature with the public key over G2. This function returns a message `msg`, a public
   key `pk`, and a signature `sig`. Verification of these test vectors should proceed as follows:
    * pk_deser = G2Decompress(pk)
    * sig_deser = G1Decompress(sig)
    * hashed_msg = G1HashToCurve(msg, "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_NUL_")
    * Check that pairing(hashed_msg, pk_deser) = pairing(sig_deser, G2Generator)
-}

g2VerifyMessage :: BuiltinByteString
g2VerifyMessage = bytesFromHex "5032ec38bbc5da98ee0c6f568b872a65a08abf251deb21bb4b56e5d8821e68aa"
{-# INLINEABLE g2VerifyMessage #-}

g2VerifyPubKey :: BuiltinByteString
g2VerifyPubKey =
  bytesFromHex
    ( "b4953c4ba10c4d4196f90169e76faf154c260ed73fc77bb65dc3be31e0cec614a7287cda94195343676c2c57494f0e65"
        <> "1527e6504c98408e599a4eb96f7c5a8cfb85d2fdc772f28504580084ef559b9b623bc84ce30562ed320f6b7f65245ad4"
    )
{-# INLINEABLE g2VerifyPubKey #-}

g2VerifySignature :: BuiltinByteString
g2VerifySignature =
  bytesFromHex
    ( "a9d4de7b0b2805fe52bccb86415ef7b8ffecb313c3c25404"
        <> "4dfc1bdc531d3eae999d87717822a052692140774bd7245c"
    )
{-# INLINEABLE g2VerifySignature #-}

g2VerifyScript
  :: BuiltinByteString
  -> BuiltinByteString
  -> BuiltinByteString
  -> BuiltinByteString
  -> Bool
g2VerifyScript message pubKey signature dst =
  let g2generator = Tx.bls12_381_G2_uncompress Tx.bls12_381_G2_compressed_generator
      pkDeser = Tx.bls12_381_G2_uncompress pubKey
      sigDeser = Tx.bls12_381_G1_uncompress signature
      hashedMsg = Tx.bls12_381_G1_hashToGroup message dst
   in Tx.bls12_381_finalVerify (Tx.bls12_381_millerLoop hashedMsg pkDeser) (Tx.bls12_381_millerLoop sigDeser g2generator)
{-# INLINEABLE g2VerifyScript #-}

checkG2VerifyScript :: Bool
checkG2VerifyScript =
  g2VerifyScript g2VerifyMessage g2VerifyPubKey g2VerifySignature blsSigBls12381G2XmdSha256SswuRoNul

mkG2VerifyPolicy :: UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkG2VerifyPolicy =
  Tx.getPlcNoAnn
    $ $$(Tx.compile [||g2VerifyScript||])
    `Tx.unsafeApplyCode` Tx.liftCodeDef g2VerifyMessage
    `Tx.unsafeApplyCode` Tx.liftCodeDef g2VerifyPubKey
    `Tx.unsafeApplyCode` Tx.liftCodeDef g2VerifySignature
    `Tx.unsafeApplyCode` Tx.liftCodeDef blsSigBls12381G2XmdSha256SswuRoNul

---------------- Aggregate signature with single key and different messages over G1 ----------------

{- Aggregate BLS signature with the same key and different messages, with public key over G1. This
   function returns a list of 10 messages {`msg_1`, ..., `msg_10`}, a public key `pk`, and an
   aggregate signature `aggr_sig`. To verify the correctness of the test vectors, check the
   following:
    * hashed_msg_i = G2HashToCurve(msg_i, "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_NUL_") for i in [1, 10]
    * pk_deser = G1Decompress(pk)
    * aggr_sig_deser = G2Decompress(aggr_sig)
    * aggr_msg = sum_{i\in[1,10]} hashed_msg_i
    * Check that pairing(pk_deser, aggr_msg) = pairing(G1Generator, aggr_sig_deser)
-}

aggregateSingleKeyG1Messages :: [BuiltinByteString]
aggregateSingleKeyG1Messages =
  [ bytesFromHex "2ba037cdb63cb5a7277dc5d6dc549e4e28a15c70670f0e97787c170485829264"
  , bytesFromHex "ecbf14bddeb68410f423e8849e0ce35c10d20a802bbc3d9a6ca01c386279bf01"
  , bytesFromHex "e8f75f478cb0d159db767341602fa02d3e01c3d9aacf9b686eccf1bb5ff4c8fd"
  , bytesFromHex "21473e89d50f51f9a1ced2390c72ee7e37f15728e61d1fb2c8c839495e489052"
  , bytesFromHex "8c146d00fe2e1caec31b159fc42dcd7e06865c6fa5267c6ca9c5284e651e175a"
  , bytesFromHex "362f469b6e722347de959f76533315542ffa440d37cde8862da3b3331e53b60d"
  , bytesFromHex "73baeb620e63a2e646ea148974350aa337491e5f5fc087cb429173d1eeb74f5a"
  , bytesFromHex "73acc6c3d72b59b8bf5ab58cdcf76aa001689aac938a75b1bb25d77b5382898c"
  , bytesFromHex "4e73ba04bae3a083c8a2109f15b8c4680ae4ba1c70df5b513425349a77e95d3b"
  , bytesFromHex "565825a0227d45068e61eb90aa1a4dc414c0976911a52d46b39f40c5849e5abe"
  ]
{-# INLINEABLE aggregateSingleKeyG1Messages #-}

aggregateSingleKeyG1PubKey :: BuiltinByteString
aggregateSingleKeyG1PubKey =
  bytesFromHex
    ( "97c919babda8d928d771d107a69adfd85a75cee2cedc4afa"
        <> "4c0a7e902f38b340ea21a701a46df825210dd6942632b46c"
    )
{-# INLINEABLE aggregateSingleKeyG1PubKey #-}

aggregateSingleKeyG1Signature :: BuiltinByteString
aggregateSingleKeyG1Signature =
  bytesFromHex
    ( "b425291f423235b022cdd038e1a3cbdcc73b5a4470251634"
        <> "abb874c7585a3a05b8ea54ceb93286edb0e9184bf9a852a1"
        <> "138c6dd860e4b756c63dff65c433a6c5aa06834f00ac5a1a"
        <> "1acf6bedc44bd4354f9d36d4f20f66318f39116428fabb88"
    )
{-# INLINEABLE aggregateSingleKeyG1Signature #-}

aggregateSingleKeyG1Script
  :: [BuiltinByteString]
  -> BuiltinByteString
  -> BuiltinByteString
  -> BuiltinByteString
  -> Bool
aggregateSingleKeyG1Script messages pubKey aggregateSignature dst =
  let g1generator = Tx.bls12_381_G1_uncompress Tx.bls12_381_G1_compressed_generator
      hashedMsgs = List.map (\x -> Tx.bls12_381_G2_hashToGroup x dst) messages
      pkDeser = Tx.bls12_381_G1_uncompress pubKey
      aggrSigDeser = Tx.bls12_381_G2_uncompress aggregateSignature
      aggrMsg = foldl1 Tx.bls12_381_G2_add hashedMsgs
   in Tx.bls12_381_finalVerify (Tx.bls12_381_millerLoop pkDeser aggrMsg) (Tx.bls12_381_millerLoop g1generator aggrSigDeser)
  where
    -- PlutusTx.Foldable has no foldl1
    foldl1 :: (a -> a -> a) -> [a] -> a
    foldl1 _ [] = traceError "foldr1: empty list"
    foldl1 _ [_] = traceError "foldr1: only one element in list"
    foldl1 f (x : xs) = List.foldl f x xs
{-# INLINEABLE aggregateSingleKeyG1Script #-}

checkAggregateSingleKeyG1Script :: Bool
checkAggregateSingleKeyG1Script =
  aggregateSingleKeyG1Script
    aggregateSingleKeyG1Messages
    aggregateSingleKeyG1PubKey
    aggregateSingleKeyG1Signature
    blsSigBls12381G2XmdSha256SswuRoNul

mkAggregateSingleKeyG1Policy :: UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkAggregateSingleKeyG1Policy =
  Tx.getPlcNoAnn
    $ $$(Tx.compile [||aggregateSingleKeyG1Script||])
    `Tx.unsafeApplyCode` Tx.liftCodeDef aggregateSingleKeyG1Messages
    `Tx.unsafeApplyCode` Tx.liftCodeDef aggregateSingleKeyG1PubKey
    `Tx.unsafeApplyCode` Tx.liftCodeDef aggregateSingleKeyG1Signature
    `Tx.unsafeApplyCode` Tx.liftCodeDef blsSigBls12381G2XmdSha256SswuRoNul

---------------- Aggregate signature with multiple keys and single message over G1 ----------------

{- Aggregate BLS signature with different keys and same message, with public key over G2. This
   function returns a message `msg`, ten public keys `{pk_1,...,pk_10}`, and an
   aggregate signature `aggr_sig`. To verify the correctness of the test vectors, check the
   following:
    * hashed_msg = G1HashToCurve(msg, "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_NUL_")
    * pk_deser_i = G2Decompress(pk_i) for i in [1, 10]
    * ds_scalar = SHA256(pk_1 || .. || pk_10)[..16] (where [..16] represent the first 16 bytes)
    * aggr_sig_deser = G1Decompress(aggr_sig)
    * aggr_pk = sum_{i\in[1,10]} ds_scalar^i * pk_deser_i
    * Check that pairing(hashed_msg, aggr_pk) = pairing(aggr_sig_deser, G2Generator)
-}

aggregateMultiKeyG2Message :: BuiltinByteString
aggregateMultiKeyG2Message =
  bytesFromHex
    "e345b7f2c017b16bb335c696bc0cc302f3db897fa25365a2ead1f149d87a97e8"
{-# INLINEABLE aggregateMultiKeyG2Message #-}

aggregateMultiKeyG2PubKeys :: [BuiltinByteString]
aggregateMultiKeyG2PubKeys =
  [ bytesFromHex
      ( "83718f20d08471565b3a6ca6ea82c1928e8730f87e2afe460b74842f2880facd8e63b8abcdcd7350fe5813a08aa0efed"
          <> "13216b10de1c56dc059c3a8910bd97ae133046ae031d2a53a44e460ab71ebda94bab64ed7478cf1a91b6d3981e32fc95"
      )
  , bytesFromHex
      ( "814f825911bd066855333b74a3cc564d512503ee29ea1ec3bd57a3c07fa5768ad27ea1ddd8047f43fbc9a4ebda897c14"
          <> "06415fefbb8838b8782aa747e2fde7b1813d0f89fad06c8971041c9427abf848503e34e3ca033ba85d50b72ffac4be4a"
      )
  , bytesFromHex
      ( "9974c70513ed5538a8e55f5ce1a0267282b9e8431e25ae566950b2d0793a44a0a3c52110f4d83d694a5296615ee68573"
          <> "098c14d255783a9b1a169d2be1baefbef914a4f830a9099f720063914cc919064d2244582bb9f302eac39c8b195cf3d2"
      )
  , bytesFromHex
      ( "894a3a01d38169a38bea13097cf904dd3ff9dceefb51e8b539725a237ae55a361758be1cdf0e21a7b8db3599adaf2305"
          <> "050f1d8450b924a4b910ff536fc2f7960cd3251c2a457b975d46f7c0f74493cc9b5e8d2fed2e489363e641cc79933d1e"
      )
  , bytesFromHex
      ( "9646da0149ed140e33a99e1ffc5fe9c97c2368ca273544024993cdcb7aa04c0be936e6d4427747e62c4caea4fe1f69e5"
          <> "162fad222e0487f5556524c9d3db74921e1c0f5893f0e26c759e3873e8fd6637e6051f70ef9a3363cf284e8eee67bcf3"
      )
  , bytesFromHex
      ( "b75743fb2f8321ac56cee19aacd7e141a3592b7230992ea84d8800d45ad71924a477f61cf9d4a2783df59dac21cd17e7"
          <> "0e4ce5d526cbe73edc4a10b78fa56a2ef34d2009f2756d2d50188031e026a6a1dadcd5e753f5e7f7276048277d3819f1"
      )
  , bytesFromHex
      ( "873c1e7d525265afa8c037d33874261a90daaa2c6ed5e46ed043ec48a28b7111d0de65800aa72448c1fdb1026ba076bd"
          <> "04193bd2d04e0de63e7a008b8417420eb4920767a1d32f6330ed25bdb4dc7726d989d6cf192db6b32728bb388195ba27"
      )
  , bytesFromHex
      ( "b993f867f9f1f84c3c5c3e5b80013055da7705491c36a80e1201a6a503d7364000c50bc27e03477646874a3074cc4e39"
          <> "0febfea78a2b4d0e40c57d6deaf9fae430a19fcce0c03f43ff8f7e788de0c7b8ce1b69b69d1d026175c8f2730777866d"
      )
  , bytesFromHex
      ( "99836a204576636f34a4663cfa7e02a05cb2d4fd1b582427d199ac3ddac6f087968d2290198aa15e04f6e7e0d070b7dd"
          <> "03607db9c2e4b17709853c30b2f6490261599408fbbc17371de74d0a2a76ff10cd8c9b55461c444bbebc82547bb40c9f"
      )
  , bytesFromHex
      ( "96f8d678f40dd83b2060e14372d0bc43a423fecac44f082afd89cb481b855885ac83fb366516dc74023cc41a0c606be2"
          <> "067ba826ea612f84c9f0e895d02bc04d6c34e201ff8c26cc22cb4c426c53f503d8948eafceb12e2f4b6ad49b4e051690"
      )
  ]
{-# INLINEABLE aggregateMultiKeyG2PubKeys #-}

aggregateMultiKeyG2Signature :: BuiltinByteString
aggregateMultiKeyG2Signature =
  bytesFromHex
    ( "b24d876661d0d1190c796bf7eaa7e02b807ff603093b1733"
        <> "6289d4de0477f6c17afb487275cb9de44325016edfeda042"
    )
{-# INLINEABLE aggregateMultiKeyG2Signature #-}

aggregateMultiKeyG2Script
  :: BuiltinByteString
  -> [BuiltinByteString]
  -> BuiltinByteString
  -> BuiltinByteString
  -> BuiltinByteString
  -> Bool
aggregateMultiKeyG2Script message pubKeys aggregateSignature bs16Null dst =
  let g2generator = Tx.bls12_381_G2_uncompress Tx.bls12_381_G2_compressed_generator
      hashedMsg = Tx.bls12_381_G1_hashToGroup message dst
      pksDeser = List.map Tx.bls12_381_G2_uncompress pubKeys
      -- scalar calcuates to (142819114285630344964654001480828217341 :: Integer)
      dsScalar =
        byteStringToIntegerLE
          ( Tx.sliceByteString
              0
              16
              (Tx.sha2_256 (foldl1 Tx.appendByteString pubKeys))
              `Tx.appendByteString` bs16Null
          )
      aggrSigDeser = Tx.bls12_381_G1_uncompress aggregateSignature
      aggrPk = calcAggregatedPubkeys dsScalar pksDeser
   in Tx.bls12_381_finalVerify (Tx.bls12_381_millerLoop hashedMsg aggrPk) (Tx.bls12_381_millerLoop aggrSigDeser g2generator)
  where
    -- PlutusTx.Foldable has no foldl1
    foldl1 :: (a -> a -> a) -> [a] -> a
    foldl1 _ [] = traceError "foldr1: empty list"
    foldl1 _ [_] = traceError "foldr1: only one element in list"
    foldl1 f (x : xs) = List.foldl f x xs

    calcAggregatedPubkeys :: Integer -> [BuiltinBLS12_381_G2_Element] -> BuiltinBLS12_381_G2_Element
    calcAggregatedPubkeys dsScalar' pksDeser' =
      let dsScalars = calcDsScalars pksDeser' [dsScalar']
       in go 1 (List.drop 1 pksDeser') (List.drop 1 dsScalars) (calcAggregatedPubkey (List.head pksDeser') (List.head dsScalars))

    calcDsScalars :: [BuiltinBLS12_381_G2_Element] -> [Integer] -> [Integer]
    calcDsScalars [] acc = acc
    calcDsScalars (_ : xs) [x'] = calcDsScalars xs [x', x' * x']
    calcDsScalars (_ : xs) acc@(x' : xs') = calcDsScalars xs (acc List.++ [List.last xs' * x'])
    calcDsScalars _ _ = traceError "calcDsScalars: unexpected"

    go :: Integer -> [BuiltinBLS12_381_G2_Element] -> [Integer] -> BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element
    go _ [] _ acc = acc
    go i (x : xs) (x' : xs') acc = go (i + 1) xs xs' (acc `Tx.bls12_381_G2_add` (calcAggregatedPubkey x x'))
    go _ _ _ _ = traceError "go: unexpected"

    calcAggregatedPubkey :: BuiltinBLS12_381_G2_Element -> Integer -> BuiltinBLS12_381_G2_Element
    calcAggregatedPubkey pk ds = ds `Tx.bls12_381_G2_scalarMul` pk
{-# INLINEABLE aggregateMultiKeyG2Script #-}

{- An alternative implementation of calcAggregatedPubkeys which uses a different
-- means of scalar exponentiation. It results in a slightly smaller script using less CPU but
-- considerably more memory, so the overall cost is a greater.
-- Worth keeping for reference because it is simpler and more readble than the implementation used above.
-}
--      calcAggregatedPubkeys dsScalar' pksDeser' =
--        go 1 (drop 1 pksDeser') (calc (head pksDeser') 0)
--        where
--          calc pk i = (dsScalar' `power` (i + 1)) `Tx.bls12_381_G2_scalarMul` pk
--          go _ [] acc     = acc
--          go i (x:xs) acc = go (i + 1) xs (acc `Tx.bls12_381_G2_add` (calc x i))
--
--      power :: Integer -> Integer -> Integer
--      power x n
--        | n == 0 = 1
--        | n > 0 = x * power x (n - 1)
--        | otherwise = 0

checkAggregateMultiKeyG2Script :: Bool
checkAggregateMultiKeyG2Script =
  aggregateMultiKeyG2Script
    aggregateMultiKeyG2Message
    aggregateMultiKeyG2PubKeys
    aggregateMultiKeyG2Signature
    byteString16Null
    blsSigBls12381G2XmdSha256SswuRoNul

mkAggregateMultiKeyG2Policy :: UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkAggregateMultiKeyG2Policy =
  Tx.getPlcNoAnn
    $ $$(Tx.compile [||aggregateMultiKeyG2Script||])
    `Tx.unsafeApplyCode` Tx.liftCodeDef aggregateMultiKeyG2Message
    `Tx.unsafeApplyCode` Tx.liftCodeDef aggregateMultiKeyG2PubKeys
    `Tx.unsafeApplyCode` Tx.liftCodeDef aggregateMultiKeyG2Signature
    `Tx.unsafeApplyCode` Tx.liftCodeDef byteString16Null
    `Tx.unsafeApplyCode` Tx.liftCodeDef blsSigBls12381G2XmdSha256SswuRoNul

---------------- Schnorr signature in G1 ----------------

{- Schnorr signature in G1. This function returns a message `msg`, a public key `pk` and a
   signature `(A, r)`. To verify the signature, proceed as follows:
    * c = Sha256(A || pk || msg)[..16]
    * pk_deser = G1Decompress(pk)
    * A_deser = G1Decompress(A)
    * r_deser = IntegerFromBytes(r)
    * Check that r_deser * G1Generator = A_deser + c * pk_deser
-}

schnorrG1VerifyMessage :: BuiltinByteString
schnorrG1VerifyMessage = bytesFromHex "0558db9aff738e5421439601e7f30e88b74f43b80c1d172b5d371ce0dc05c912"
{-# INLINEABLE schnorrG1VerifyMessage #-}

schnorrG1VerifyPubKey :: BuiltinByteString
schnorrG1VerifyPubKey =
  bytesFromHex
    ( "b91cacee903a53383c504e9e9a39e57d1eaa6403d5d38fc9"
        <> "496e5007d54ca92d106d1059f09461972aa98514d07000ae"
    )
{-# INLINEABLE schnorrG1VerifyPubKey #-}

schnorrG1VerifySignature :: (BuiltinByteString, BuiltinByteString)
schnorrG1VerifySignature =
  ( bytesFromHex
      "8477e8491acc1cfbcf675acf7cf6b92e027cad7dd604a0e8205703aa2cc590066c1746f89e10d492d0230e6620c29726"
  , bytesFromHex "4e908280c0100cfe53501171ffa93528b9e2bb551d1025decb4a5b416a0aee53"
  )
{-# INLINEABLE schnorrG1VerifySignature #-}

schnorrG1VerifyScript
  :: BuiltinByteString
  -> BuiltinByteString
  -> (BuiltinByteString, BuiltinByteString)
  -> BuiltinByteString
  -> Bool
schnorrG1VerifyScript message pubKey signature bs16Null =
  let a = Tx.fst signature
      r = Tx.snd signature
      c =
        byteStringToIntegerLE
          ( Tx.sliceByteString
              0
              16
              (Tx.sha2_256 (a `Tx.appendByteString` pubKey `Tx.appendByteString` message))
              `Tx.appendByteString` bs16Null
          )
      pkDeser = Tx.bls12_381_G1_uncompress pubKey
      aDeser = Tx.bls12_381_G1_uncompress a
      rDeser = byteStringToIntegerLE r
      g1generator = Tx.bls12_381_G1_uncompress Tx.bls12_381_G1_compressed_generator
   in (rDeser `Tx.bls12_381_G1_scalarMul` g1generator)
        == (aDeser `Tx.bls12_381_G1_add` (c `Tx.bls12_381_G1_scalarMul` pkDeser))
        -- additional check using negation is for testing the function
        -- it can be removed to improve performance
        && (rDeser `Tx.bls12_381_G1_scalarMul` g1generator)
        `Tx.bls12_381_G1_add` (Tx.bls12_381_G1_neg aDeser)
        == c
        `Tx.bls12_381_G1_scalarMul` pkDeser
{-# INLINEABLE schnorrG1VerifyScript #-}

checkSchnorrG1VerifyScript :: Bool
checkSchnorrG1VerifyScript =
  schnorrG1VerifyScript
    schnorrG1VerifyMessage
    schnorrG1VerifyPubKey
    schnorrG1VerifySignature
    byteString16Null

mkSchnorrG1VerifyPolicy :: UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkSchnorrG1VerifyPolicy =
  Tx.getPlcNoAnn
    $ $$(Tx.compile [||schnorrG1VerifyScript||])
    `Tx.unsafeApplyCode` Tx.liftCodeDef schnorrG1VerifyMessage
    `Tx.unsafeApplyCode` Tx.liftCodeDef schnorrG1VerifyPubKey
    `Tx.unsafeApplyCode` Tx.liftCodeDef schnorrG1VerifySignature
    `Tx.unsafeApplyCode` Tx.liftCodeDef byteString16Null

---------------- Schnorr signature in G2 ----------------

{- Schnorr signature in G2. This function returns a message `msg`, a public key `pk` and a
   signature `(A, r)`.To verify the signature, proceed as follows:
    * hash = Sha256(A || pk || msg)[..16]
    * pk_deser = G2Decompress(pk)
    * A_deser = G2Decompress(A)
    * r_deser = IntegerFromBytes(r)
    * Check that r_deser * G2Generator = A_deser + c * pk_deser
-}

schnorrG2VerifyMessage :: BuiltinByteString
schnorrG2VerifyMessage = bytesFromHex "2b71175d0486006a33f14bc4e1fe711a3d4a3a3549b230013240e8f80e54372f"
{-# INLINEABLE schnorrG2VerifyMessage #-}

schnorrG2VerifyPubKey :: BuiltinByteString
schnorrG2VerifyPubKey =
  bytesFromHex
    ( "88370a4b4ddc627613b0396498fb068f1c1ff8f2aa6b946a9fc65f930d24394ddc45042e602094f6a88d49a8a037e781"
        <> "08dce014586ff5ff5744842f382e3917d180c7eb969585748d20ae8c6e07ca786e8da7ea2c7bdef5ae1becebe4da59ad"
    )
{-# INLINEABLE schnorrG2VerifyPubKey #-}

schnorrG2VerifySignature :: (BuiltinByteString, BuiltinByteString)
schnorrG2VerifySignature =
  ( bytesFromHex
      ( "964851eb8823492c8720bf8c515b87043f5bab648000e63cfb6fc6fcdf6709061e0035c315cd23d239866471dea907d9"
          <> "1568b69297dc8c4360f65d0bd399c2de19781c13bbf3a82ff1fcab8ac9f688ed96d6f2ea9a8ed057e76f0347d858ae22"
      )
  , bytesFromHex "2c5a22cb1e2fb77586c0c6908060b38107675a6277b8a61b1d6394a162af6718"
  )
{-# INLINEABLE schnorrG2VerifySignature #-}

schnorrG2VerifyScript
  :: BuiltinByteString
  -> BuiltinByteString
  -> (BuiltinByteString, BuiltinByteString)
  -> BuiltinByteString
  -> Bool
schnorrG2VerifyScript message pubKey signature bs16Null =
  let a = Tx.fst signature
      r = Tx.snd signature
      c =
        byteStringToIntegerLE
          ( Tx.sliceByteString
              0
              16
              (Tx.sha2_256 (a `Tx.appendByteString` pubKey `Tx.appendByteString` message))
              `Tx.appendByteString` bs16Null
          )
      pkDeser = Tx.bls12_381_G2_uncompress pubKey
      aDeser = Tx.bls12_381_G2_uncompress a
      rDeser = byteStringToIntegerLE r
      g2generator = Tx.bls12_381_G2_uncompress Tx.bls12_381_G2_compressed_generator
   in rDeser
        `Tx.bls12_381_G2_scalarMul` g2generator
        == (aDeser `Tx.bls12_381_G2_add` (c `Tx.bls12_381_G2_scalarMul` pkDeser))
        -- additional check using negation is for testing the function
        -- it can be removed to improve performance
        && (rDeser `Tx.bls12_381_G2_scalarMul` g2generator)
        `Tx.bls12_381_G2_add` (Tx.bls12_381_G2_neg aDeser)
        == c
        `Tx.bls12_381_G2_scalarMul` pkDeser
{-# INLINEABLE schnorrG2VerifyScript #-}

checkSchnorrG2VerifyScript :: Bool
checkSchnorrG2VerifyScript =
  schnorrG2VerifyScript
    schnorrG2VerifyMessage
    schnorrG2VerifyPubKey
    schnorrG2VerifySignature
    byteString16Null

mkSchnorrG2VerifyPolicy :: UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkSchnorrG2VerifyPolicy =
  Tx.getPlcNoAnn
    $ $$(Tx.compile [||schnorrG2VerifyScript||])
    `Tx.unsafeApplyCode` Tx.liftCodeDef schnorrG2VerifyMessage
    `Tx.unsafeApplyCode` Tx.liftCodeDef schnorrG2VerifyPubKey
    `Tx.unsafeApplyCode` Tx.liftCodeDef schnorrG2VerifySignature
    `Tx.unsafeApplyCode` Tx.liftCodeDef byteString16Null
