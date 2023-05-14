-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}

{- | Approximations of the sort of computations involving BLS12-381 primitives
 that one might wish to perform on the chain.  Real on-chain code will have
 extra overhead, but these examples help to give us an idea of the sort of
 computation that can feasibly be carried out within the validation budget
 limits. -}
module PlutusBenchmark.BLS12_381.Common ( UProg
                                        , UTerm
                                        , checkGroth16Verify_Haskell
                                        , listOfSizedByteStrings
                                        , mkGroth16VerifyScript
                                        , mkHashAndAddG1Script
                                        , mkHashAndAddG2Script
                                        , mkPairingScript
                                        , mkUncompressAndAddG1Script
                                        , mkUncompressAndAddG2Script
                                        , toAnonDeBruijnProg
                                        )
where
import PlutusCore (DefaultFun, DefaultUni)
import PlutusTx qualified as Tx
import UntypedPlutusCore qualified as UPLC

import PlutusTx.Prelude as Tx hiding (sort, (*))

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Word (Word8)
import Hedgehog.Internal.Gen qualified as G
import Hedgehog.Internal.Range qualified as R
import System.IO.Unsafe (unsafePerformIO)

import Prelude (fromIntegral)

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

-- Create a list containing n bytestrings of length l.  This could be better.
listOfSizedByteStrings :: Integer -> Integer -> [ByteString]
listOfSizedByteStrings n l = unsafePerformIO . G.sample $
                             G.list (R.singleton $ fromIntegral n)
                                  (G.bytes (R.singleton $ fromIntegral l))

---------------- Examples ----------------

-- Hash some bytestrings onto G1 and add them all together

{-# INLINABLE hashAndAddG1 #-}
hashAndAddG1 :: [BuiltinByteString] -> BuiltinBLS12_381_G1_Element
hashAndAddG1 [] = error ()
hashAndAddG1 (p:ps) =
    go ps (Tx.bls12_381_G1_hashToGroup p emptyByteString)
    where go [] acc     = acc
          go (q:qs) acc = go qs $ Tx.bls12_381_G1_add (Tx.bls12_381_G1_hashToGroup q emptyByteString) acc

mkHashAndAddG1Script :: [ByteString] -> UProg
mkHashAndAddG1Script l =
    let points = map toBuiltin l
    in Tx.getPlcNoAnn $ $$(Tx.compile [|| hashAndAddG1 ||]) `Tx.unsafeApplyCode` Tx.liftCodeDef points

-- Hash some bytestrings onto G2 and add them all together
{-# INLINABLE hashAndAddG2 #-}
hashAndAddG2 :: [BuiltinByteString] -> BuiltinBLS12_381_G2_Element
hashAndAddG2 [] = error ()
hashAndAddG2 (p:ps) =
    go ps (Tx.bls12_381_G2_hashToGroup p emptyByteString)
    where go [] acc     = acc
          go (q:qs) acc = go qs $ Tx.bls12_381_G2_add (Tx.bls12_381_G2_hashToGroup q emptyByteString) acc

mkHashAndAddG2Script :: [ByteString] -> UProg
mkHashAndAddG2Script l =
    let points = map toBuiltin l
    in Tx.getPlcNoAnn $ $$(Tx.compile [|| hashAndAddG2 ||]) `Tx.unsafeApplyCode` Tx.liftCodeDef points

-- Uncompress a list of compressed G1 points and add them all together
{-# INLINABLE uncompressAndAddG1 #-}
uncompressAndAddG1 :: [BuiltinByteString] -> BuiltinBLS12_381_G1_Element
uncompressAndAddG1 [] = error ()
uncompressAndAddG1 (p:ps) =
    go ps (Tx.bls12_381_G1_uncompress p)
    where go [] acc     = acc
          go (q:qs) acc = go qs $ Tx.bls12_381_G1_add (Tx.bls12_381_G1_uncompress q) acc

mkUncompressAndAddG1Script :: [ByteString] -> UProg
mkUncompressAndAddG1Script l =
    let ramdomPoint bs = Tx.bls12_381_G1_hashToGroup bs emptyByteString
        points = map (Tx.bls12_381_G1_compress . ramdomPoint . toBuiltin) l
    in Tx.getPlcNoAnn $ $$(Tx.compile [|| uncompressAndAddG1 ||]) `Tx.unsafeApplyCode` Tx.liftCodeDef points

-- Uncompress a list of compressed G1 points and add them all together
{-# INLINABLE uncompressAndAddG2 #-}
uncompressAndAddG2 :: [BuiltinByteString] -> BuiltinBLS12_381_G2_Element
uncompressAndAddG2 [] = error ()
uncompressAndAddG2 (p:ps) =
    go ps (Tx.bls12_381_G2_uncompress p)
    where go [] acc     = acc
          go (q:qs) acc = go qs $ Tx.bls12_381_G2_add (Tx.bls12_381_G2_uncompress q) acc

mkUncompressAndAddG2Script :: [ByteString] -> UProg
mkUncompressAndAddG2Script l =
    let ramdomPoint bs = Tx.bls12_381_G2_hashToGroup bs emptyByteString
        points = map (Tx.bls12_381_G2_compress . ramdomPoint . toBuiltin) l
    in Tx.getPlcNoAnn $ $$(Tx.compile [|| uncompressAndAddG2 ||]) `Tx.unsafeApplyCode` Tx.liftCodeDef points

-- Pairing operations

-- Take two points p1 and p2 in G1 and two points q1 and q2 in G2, apply the
-- Miller loop to (p1,q1) and (p2,q2), and then call finalVerify on the results.
{-# INLINABLE runPairingFunctions #-}
runPairingFunctions
    :: Tx.BuiltinBLS12_381_G1_Element
    -> Tx.BuiltinBLS12_381_G2_Element
    -> Tx.BuiltinBLS12_381_G1_Element
    -> Tx.BuiltinBLS12_381_G2_Element
    -> Bool
runPairingFunctions p1 q1 p2 q2 =
    let r1 = Tx.bls12_381_millerLoop p1 q1
        r2 = Tx.bls12_381_millerLoop p2 q2
    in Tx.bls12_381_finalVerify r1 r2

mkPairingScript
    :: BuiltinBLS12_381_G1_Element
    -> BuiltinBLS12_381_G2_Element
    -> BuiltinBLS12_381_G1_Element
    -> BuiltinBLS12_381_G2_Element
    -> UProg
mkPairingScript p1 q1 p2 q2 =
    Tx.getPlcNoAnn $ $$(Tx.compile [|| runPairingFunctions ||])
          `Tx.unsafeApplyCode` Tx.liftCodeDef p1
          `Tx.unsafeApplyCode` Tx.liftCodeDef q1
          `Tx.unsafeApplyCode` Tx.liftCodeDef p2
          `Tx.unsafeApplyCode` Tx.liftCodeDef q2

---------------- Groth16 verification ----------------

{- | An example of the on-chain computation required for verification of a Groth16
 proof.  The data here is derived from
 https://github.com/achimcc/groth16-example/blob/main/src/lib.rs -}

-- Wrappers for compressed group elements for slightly better type safety
newtype CompressedG1Element = CompressedG1Element { g1 :: BuiltinByteString }
    deriving newtype (Tx.Lift DefaultUni)

mkG1Element :: [Word8] -> CompressedG1Element
mkG1Element = CompressedG1Element . toBuiltin . BS.pack

newtype CompressedG2Element = CompressedG2Element { g2 :: BuiltinByteString }
    deriving newtype (Tx.Lift DefaultUni)

mkG2Element :: [Word8] -> CompressedG2Element
mkG2Element = CompressedG2Element . toBuiltin . BS.pack

scalar :: Integer
scalar = 0x1884d0cbcc5947434e46d19b3e904e18a8ee8d0d39ce9d315f3b00e338c8f618

-- Lots of group elements for input to the computation

alpha :: CompressedG1Element
alpha = mkG1Element [ 0xb7, 0x1d, 0xb1, 0xfa, 0x5f, 0x41, 0x36, 0x2e
                    , 0x93, 0x02, 0x5b, 0x35, 0x56, 0xd7, 0x6e, 0xad
                    , 0x12, 0x25, 0xcf, 0x59, 0x0d, 0x1c, 0xdb, 0x9e
                    , 0x38, 0x2a, 0x1f, 0xeb, 0xb7, 0x96, 0x3d, 0xcd
                    , 0x24, 0xa5, 0x1e, 0x18, 0xdf, 0x04, 0xab, 0x22
                    , 0x1b, 0xec, 0xaf, 0x29, 0x16, 0x9f, 0xaf, 0x25 ]

beta :: CompressedG2Element
beta = mkG2Element [ 0xb3, 0xa2, 0x6b, 0x0b, 0x47, 0x12, 0xe7, 0x8d
                   , 0x5d, 0x71, 0x78, 0x6d, 0x96, 0x13, 0x2a, 0x7c
                   , 0x58, 0x50, 0x23, 0xa3, 0x66, 0x32, 0xca, 0xda
                   , 0x44, 0x17, 0x1a, 0xc3, 0xf4, 0x5d, 0xb5, 0x24
                   , 0xc3, 0xf6, 0x57, 0x0c, 0x8a, 0x3f, 0x7d, 0xec
                   , 0x35, 0xae, 0x1a, 0xc3, 0x30, 0x9b, 0x05, 0xdd
                   , 0x0b, 0x30, 0x6d, 0xb4, 0xf7, 0x4f, 0xd9, 0xec
                   , 0x42, 0x1c, 0xa7, 0x0c, 0x54, 0x42, 0x5d, 0x92
                   , 0x2e, 0xac, 0x4c, 0x40, 0x3b, 0x00, 0xdb, 0x91
                   , 0x6f, 0xde, 0xdf, 0x06, 0x5b, 0xdc, 0xe0, 0x0e
                   , 0xce, 0x17, 0xb9, 0x7a, 0x4e, 0x97, 0x17, 0x3e
                   , 0x4d, 0x59, 0x89, 0x81, 0x8e, 0xdf, 0xaa, 0x4c ]

gamma :: CompressedG2Element
gamma = mkG2Element [ 0xb5, 0xac, 0xb8, 0x00, 0xcd, 0x49, 0xed, 0x8c
                    , 0xbd, 0xdb, 0xf4, 0x91, 0xa1, 0xfc, 0xf8, 0xab
                    , 0xfc, 0x93, 0xf0, 0x9d, 0x38, 0xbb, 0xb2, 0xec
                    , 0xb6, 0xb0, 0x8e, 0x23, 0xa4, 0x64, 0x2c, 0xe5
                    , 0x9c, 0x9b, 0x03, 0x86, 0x53, 0x9a, 0xc3, 0xce
                    , 0xcd, 0xfb, 0x66, 0xa9, 0xf0, 0x27, 0xfc, 0x21
                    , 0x0f, 0x25, 0x95, 0x10, 0x75, 0x64, 0x44, 0xbc
                    , 0x5e, 0xef, 0x65, 0x4f, 0x4d, 0x06, 0x12, 0xb5
                    , 0xd6, 0x37, 0x5f, 0x95, 0x26, 0xb1, 0xb9, 0x66
                    , 0xce, 0x53, 0xb8, 0xf1, 0x25, 0x94, 0xe1, 0xb3
                    , 0x99, 0xd0, 0x82, 0x31, 0xcf, 0xe6, 0xc2, 0x69
                    , 0xa4, 0x4a, 0xa8, 0xd5, 0x87, 0xf2, 0x36, 0x9d ]

delta :: CompressedG2Element
delta = mkG2Element [ 0xb3, 0xaa, 0x79, 0x7b, 0xaf, 0xa3, 0x9a, 0x48
                    , 0xf6, 0xf8, 0x7c, 0x24, 0x83, 0xc8, 0x94, 0xc2
                    , 0x81, 0xc8, 0x07, 0x82, 0x1c, 0x47, 0x30, 0x1f
                    , 0xfb, 0x75, 0x5a, 0xcf, 0xcf, 0xd2, 0x2c, 0x23
                    , 0x23, 0xce, 0xdf, 0x63, 0x49, 0xc7, 0xfe, 0xdd
                    , 0x32, 0x00, 0xa4, 0xae, 0x55, 0x86, 0x31, 0xe5
                    , 0x01, 0xd2, 0x99, 0xeb, 0x93, 0x13, 0x5c, 0x07
                    , 0xcf, 0x69, 0x4c, 0xa1, 0x18, 0xd1, 0xb3, 0x86
                    , 0x49, 0x05, 0x29, 0xc6, 0x0f, 0x57, 0x93, 0x5c
                    , 0xef, 0xa8, 0x9f, 0xca, 0xfa, 0x13, 0xa8, 0x3f
                    , 0x84, 0x20, 0x7b, 0x76, 0xfe, 0x07, 0x8d, 0xc8
                    , 0x59, 0xd4, 0x02, 0x74, 0x3d, 0x46, 0x8c, 0x15 ]

gamma_abc_1 :: CompressedG1Element
gamma_abc_1 = mkG1Element [ 0xb7, 0xf6, 0xd0, 0x6d, 0xd3, 0xe5, 0x24, 0x6e
                          , 0xf6, 0xb5, 0x1b, 0x07, 0x5c, 0x30, 0xb6, 0x8f
                          , 0xd4, 0x90, 0xfb, 0xf8, 0x5e, 0x02, 0x05, 0xf7
                          , 0x9f, 0xa0, 0x4d, 0x81, 0x13, 0x31, 0x92, 0x13
                          , 0x94, 0x63, 0xb5, 0xe8, 0xef, 0xb2, 0x2c, 0x39
                          , 0xef, 0x3d, 0xd1, 0xc5, 0x09, 0x20, 0x15, 0xb8 ]

gamma_abc_2 :: CompressedG1Element
gamma_abc_2 = mkG1Element [ 0xa2, 0xe6, 0x37, 0xdb, 0xff, 0x52, 0xa1, 0xe4
                          , 0xa8, 0xc5, 0xd9, 0x85, 0xb3, 0x41, 0x1f, 0xc5
                          , 0xfd, 0x44, 0xaf, 0x60, 0x7e, 0x42, 0x92, 0x3e
                          , 0xab, 0xb4, 0x7a, 0xd8, 0x76, 0xe1, 0xf0, 0x2b
                          , 0x5b, 0xe0, 0x34, 0xad, 0xaf, 0x73, 0x95, 0x2a
                          , 0xe8, 0xaf, 0xfe, 0xe5, 0xf5, 0x18, 0x41, 0xde ]

a :: CompressedG1Element
a = mkG1Element [ 0xa0, 0x5b, 0xe5, 0x0f, 0xab, 0x57, 0x95, 0xbb
                , 0x87, 0x84, 0x39, 0x3a, 0x50, 0x45, 0xf9, 0x87
                , 0x47, 0x17, 0x3a, 0xd2, 0x87, 0xf5, 0x5e, 0x21
                , 0x34, 0x71, 0xbd, 0x55, 0x97, 0x45, 0x55, 0x14
                , 0x52, 0x45, 0x3c, 0x4c, 0x3a, 0x39, 0xe7, 0xc8
                , 0x83, 0x10, 0x84, 0x9f, 0x3c, 0x7a, 0x1f, 0xc3 ]

b :: CompressedG2Element
b = mkG2Element [ 0xad, 0x63, 0x48, 0xb6, 0xb7, 0xb3, 0x4c, 0x86
                , 0xbf, 0x37, 0xa7, 0x48, 0xcd, 0x2d, 0x82, 0xa2
                , 0x50, 0xdf, 0xc6, 0x48, 0x46, 0x75, 0x66, 0x88
                , 0x25, 0xa1, 0x6f, 0x7d, 0xa6, 0xa0, 0x4d, 0x34
                , 0x24, 0x11, 0x3e, 0x32, 0x5c, 0xe7, 0x34, 0xec
                , 0x44, 0x95, 0x60, 0x82, 0xc0, 0xa0, 0x6e, 0x5f
                , 0x18, 0x68, 0xe1, 0xf1, 0xa6, 0xe5, 0x59, 0xb9
                , 0xfe, 0x81, 0xf1, 0xa9, 0x01, 0xf8, 0xa6, 0x34
                , 0x1b, 0x30, 0x1c, 0x45, 0xb2, 0x5d, 0x30, 0x80
                , 0xfb, 0xc5, 0x03, 0x93, 0x53, 0xd8, 0xf7, 0x1b
                , 0x55, 0x0b, 0x27, 0x4e, 0xc4, 0xc0, 0x7c, 0x70
                , 0xcd, 0x11, 0x53, 0x56, 0x2c, 0x31, 0x4c, 0x97 ]

c :: CompressedG1Element
c = mkG1Element [ 0xb5, 0x69, 0xcc, 0x49, 0x1b, 0x4d, 0xf0, 0x35
                , 0xcb, 0xf4, 0x9e, 0x95, 0x1f, 0xd4, 0xfe, 0x30
                , 0xaa, 0x82, 0x36, 0xb0, 0xe2, 0xaf, 0x68, 0xf4
                , 0xc1, 0x59, 0x2c, 0xd4, 0x0d, 0xeb, 0xeb, 0x71
                , 0x8a, 0xf3, 0x36, 0x39, 0xdb, 0x6b, 0xc1, 0xe2
                , 0xda, 0x9d, 0x98, 0xe5, 0x53, 0xe5, 0xea, 0xed ]

{-# INLINABLE groth16Verify #-}
groth16Verify
    :: BuiltinByteString  -- G1
    -> BuiltinByteString  -- G2
    -> BuiltinByteString  -- G2
    -> BuiltinByteString  -- G1
    -> BuiltinByteString  -- G1
    -> BuiltinByteString  -- G1
    -> BuiltinByteString  -- G1
    -> BuiltinByteString  -- G2
    -> BuiltinByteString  -- G1
    -> Integer
    -> Bool
groth16Verify (Tx.bls12_381_G1_uncompress -> alpha')
              (Tx.bls12_381_G2_uncompress -> beta')
              (Tx.bls12_381_G2_uncompress -> gamma')
              (Tx.bls12_381_G2_uncompress -> delta')
              (Tx.bls12_381_G1_uncompress -> abc1')
              (Tx.bls12_381_G1_uncompress -> abc2')
              (Tx.bls12_381_G1_uncompress -> a')
              (Tx.bls12_381_G2_uncompress -> b')
              (Tx.bls12_381_G1_uncompress -> c')
              s =
                  let l1 = Tx.bls12_381_millerLoop a' b'
                      l2 = Tx.bls12_381_millerLoop alpha' beta'
                      l3 = Tx.bls12_381_millerLoop c' delta'
                      p  = Tx.bls12_381_G1_add  abc1' (Tx.bls12_381_G1_scalarMul s abc2')
                      l4 = Tx.bls12_381_millerLoop p gamma'
                      y  = Tx.bls12_381_mulMlResult l2 (Tx.bls12_381_mulMlResult l3 l4)
                  in Tx.bls12_381_finalVerify l1 y

{- | Make a UPLC script applying groth16Verify to the inputs.  Passing the
 newtype inputs increases the size and CPU cost slightly, so we unwrap them
 first.  This should return `True`. -}
mkGroth16VerifyScript :: UProg
mkGroth16VerifyScript =
    Tx.getPlcNoAnn $ $$(Tx.compile [|| groth16Verify ||])
           `Tx.unsafeApplyCode` (Tx.liftCodeDef $ g1 alpha)
           `Tx.unsafeApplyCode` (Tx.liftCodeDef $ g2 beta)
           `Tx.unsafeApplyCode` (Tx.liftCodeDef $ g2 gamma)
           `Tx.unsafeApplyCode` (Tx.liftCodeDef $ g2 delta)
           `Tx.unsafeApplyCode` (Tx.liftCodeDef $ g1 gamma_abc_1)
           `Tx.unsafeApplyCode` (Tx.liftCodeDef $ g1 gamma_abc_2)
           `Tx.unsafeApplyCode` (Tx.liftCodeDef $ g1 a)
           `Tx.unsafeApplyCode` (Tx.liftCodeDef $ g2 b)
           `Tx.unsafeApplyCode` (Tx.liftCodeDef $ g1 c)
           `Tx.unsafeApplyCode` Tx.liftCodeDef scalar

-- | Check that the Haskell version returns the correct result.
checkGroth16Verify_Haskell :: Bool
checkGroth16Verify_Haskell =
    groth16Verify (g1 alpha) (g2 beta) (g2 gamma) (g2 delta)
                      (g1 gamma_abc_1) (g1 gamma_abc_2) (g1 a) (g2 b) (g1 c) scalar

