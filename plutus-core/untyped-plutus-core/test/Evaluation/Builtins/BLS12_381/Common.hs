{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Evaluation.Builtins.BLS12_381.Common
where

import Crypto.BLS12_381.G1 qualified as G1
import Crypto.BLS12_381.G2 qualified as G2
import Evaluation.Builtins.Common

import Crypto.External.EllipticCurve.BLS12_381 (BLSTError)
import PlutusCore as PLC
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.MkPlc (builtin, mkConstant, mkIterApp)
import UntypedPlutusCore as UPLC

import PlutusCore.Generators.QuickCheck.Builtin
import Test.QuickCheck hiding ((.&.))

import Data.Bits (complement, xor, (.&.), (.|.))
import Data.ByteString as BS (ByteString, cons, pack, uncons)
import Data.Word (Word8)
import Text.Printf (printf)

-- PLC utilities

-- Evaluating PLC terms

type PlcTerm = PLC.Term TyName Name DefaultUni DefaultFun ()
type UplcTerm = UPLC.Term Name DefaultUni DefaultFun ()

data CekResult =
    TypeCheckEvaluateError (Error DefaultUni DefaultFun ())
  | CekError
  | CekSuccess UplcTerm
    deriving stock (Eq, Show)

evalTerm :: PlcTerm -> CekResult
evalTerm term =
    case typecheckEvaluateCekNoEmit DefaultFunV1 defaultBuiltinCostModel term
    of Left e -> TypeCheckEvaluateError e
       Right x  ->
           case x of
             EvaluationFailure   -> CekError
             EvaluationSuccess s -> CekSuccess s

-- Constructing PLC constants and applications

uplcTrue :: CekResult
uplcTrue = CekSuccess $ mkConstant () True

uplcFalse :: CekResult
uplcFalse = CekSuccess $ mkConstant () False

integer :: Integer -> PlcTerm
integer = mkConstant ()

bytestring :: ByteString -> PlcTerm
bytestring = mkConstant ()

mkApp1 :: DefaultFun -> PlcTerm -> PlcTerm
mkApp1 b x = mkIterApp () (builtin () b) [x]

mkApp2 :: DefaultFun -> PlcTerm -> PlcTerm -> PlcTerm
mkApp2 b x y = mkIterApp () (builtin () b) [x,y]

-- Constructing pairing terms

millerLoopPlc :: PlcTerm -> PlcTerm -> PlcTerm
millerLoopPlc = mkApp2 Bls12_381_millerLoop

mulMlResultPlc :: PlcTerm -> PlcTerm -> PlcTerm
mulMlResultPlc = mkApp2 Bls12_381_mulMlResult

finalVerifyPlc :: PlcTerm -> PlcTerm -> PlcTerm
finalVerifyPlc = mkApp2 Bls12_381_finalVerify

-- ByteString utilities

-- The most siginificant bit of a serialised curve point is set if the
-- serialised point is in compressed form (x-coordinate only)
compressionBit :: Word8
compressionBit = 0x80

-- The second most significant bit is set if and only if the point is the point
-- at infinity (the zero of the group); if it is set, all other bits should be zero.
infinityBit :: Word8
infinityBit = 0x40

-- The third most significant bit of a compressed point denotes the "sign" of
-- the y-coordinate of the associated point : it is set if and only if point is
-- not the point at infinity and the y-coordinate is the lexicographically
-- larger one with the given x coordinate.
signBit :: Word8
signBit = 0x20

unsafeUnconsBS :: ByteString -> (Word8, ByteString)
unsafeUnconsBS b =
    case BS.uncons b of
      Nothing -> error "Tried to uncons empty bytestring"
      Just p  -> p

-- Apply some function to the most significant byte of a bytestring
modifyMSB :: (Word8 -> Word8) -> ByteString -> ByteString
modifyMSB f s =
    let (w,rest) = unsafeUnconsBS s
    in BS.cons (f w) rest

flipBits :: Word8 -> ByteString -> ByteString
flipBits mask = modifyMSB (mask `xor`)

clearBits :: Word8 -> ByteString -> ByteString
clearBits mask = modifyMSB ((complement mask) .&.)

setBits :: Word8 -> ByteString -> ByteString
setBits mask = modifyMSB (mask .|.)

isSet :: Word8 -> ByteString -> Bool
isSet mask s =
    let (w,_) = unsafeUnconsBS s
    in w .&. mask /= 0

fix :: ByteString -> ByteString
fix s =
    let (_,s1) = unsafeUnconsBS s
        (_,s2) = unsafeUnconsBS s1
    in BS.cons 0x80 (BS.cons 0x00 s2)

---------------- Typeclasses for groups ----------------

-- | The code for the property tests for G1 and G2 is essentially identical, so
-- it's worth abstracting over the common features.  The blst Haskell FFI uses a
-- phantom type to do this but unfortunately we have to hide that to stop the
-- builtin machinery spotting it and then we have to re-abstract here.

-- | We could re-use the AbelianGroup class here, but that uses <> and `mempty`
-- and that's kind of confusing.
class (Eq a, Show a, Arbitrary a, ArbitraryBuiltin a) => TestableAbelianGroup a
    where
      gname      :: String
      zero       :: a
      add        :: a -> a -> a
      neg        :: a -> a
      scalarMul  :: Integer -> a -> a
      zeroP      :: PlcTerm
      addP       :: PlcTerm -> PlcTerm -> PlcTerm
      negP       :: PlcTerm -> PlcTerm
      scalarMulP :: PlcTerm -> PlcTerm -> PlcTerm
      eqP        :: PlcTerm -> PlcTerm -> PlcTerm
      toPlc      :: a -> PlcTerm

class TestableAbelianGroup a => HashAndCompress a
    where
      hashTo         :: ByteString -> a
      compress       :: a -> ByteString
      uncompress     :: ByteString -> Either BLSTError a
      compressedSize :: Int
      compressP      :: PlcTerm -> PlcTerm
      uncompressP    :: PlcTerm -> PlcTerm
      hashToGroupP   :: PlcTerm -> PlcTerm


-- | Generate an arbitrary element of G1.  It's tricky to construct such an
-- element directly without using quite low-level operations on the curve
-- because a random point on the curve is highly unlikely to be in the subgroup
-- G1, but fortunately `hashToGroup` always produces an element of the subgroup,
-- so we can produce random elements of G1 by hasing random bytestrings.
instance Arbitrary G1.Element
    where
      arbitrary = G1.hashToGroup <$> arbitrary

instance TestableAbelianGroup G1.Element
    where
      gname      = "G1"
      zero       = G1.zero
      add        = G1.add
      neg        = G1.neg
      scalarMul  = G1.scalarMul
      zeroP      = mkApp1 Bls12_381_G1_uncompress $ bytestring $ pack (0xc0 : replicate 47 0x00)
      addP       = mkApp2 Bls12_381_G1_add
      negP       = mkApp1 Bls12_381_G1_neg
      scalarMulP = mkApp2 Bls12_381_G1_scalarMul
      eqP        = mkApp2 Bls12_381_G1_equal
      toPlc      = mkConstant ()

instance HashAndCompress G1.Element
    where
      hashTo         = G1.hashToGroup
      compress       = G1.compress
      uncompress     = G1.uncompress
      compressedSize = 48
      compressP      = mkApp1 Bls12_381_G1_compress
      uncompressP    = mkApp1 Bls12_381_G1_uncompress
      hashToGroupP   = mkApp1 Bls12_381_G1_hashToGroup

-- | See the comment for the Arbitrary instance for G1.
instance Arbitrary G2.Element
    where
      arbitrary = G2.hashToGroup <$> arbitrary

instance TestableAbelianGroup G2.Element
    where
      gname      = "G2"
      zero       = G2.zero
      add        = G2.add
      neg        = G2.neg
      scalarMul  = G2.scalarMul
      zeroP      = mkApp1 Bls12_381_G2_uncompress $ bytestring $ pack (0xc0 : replicate 95 0x00)
      addP       = mkApp2 Bls12_381_G2_add
      negP       = mkApp1 Bls12_381_G2_neg
      scalarMulP = mkApp2 Bls12_381_G2_scalarMul
      eqP        = mkApp2 Bls12_381_G2_equal
      toPlc      = mkConstant ()

instance HashAndCompress G2.Element
    where
      hashTo         = G2.hashToGroup
      compress       = G2.compress
      uncompress     = G2.uncompress
      compressedSize = 96
      compressP      = mkApp1 Bls12_381_G2_compress
      uncompressP    = mkApp1 Bls12_381_G2_uncompress
      hashToGroupP   = mkApp1 Bls12_381_G2_hashToGroup

-- QuickCheck utilities

mkTestName :: forall a. TestableAbelianGroup a => String -> String
mkTestName s = printf "%s_%s" (gname @a) s

withNTests :: Testable prop => prop -> Property
withNTests = withMaxSuccess 200



