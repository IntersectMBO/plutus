{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}

module Evaluation.Builtins.BLS12_381.Common
where

import Evaluation.Builtins.Common
import PlutusCore.BLS12_381.G1 qualified as G1
import PlutusCore.BLS12_381.G2 qualified as G2

import Data.Bits
import Data.ByteString as BS (ByteString, cons, pack, unpack)
import Data.Either (isRight)
import UntypedPlutusCore as UPLC

import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range

import Crypto.EllipticCurve.BLS12_381 (BLSTError)
import PlutusCore as PLC
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults

import PlutusCore.MkPlc (builtin, mkConstant, mkIterApp)


---------------- Typeclasses for groups ----------------

-- | The code for the property tests for G1 and G2 is essentially identical, so
-- it's worth abstracting over the common features.  The blst Haskell FFI uses a
-- phantom type to do this but unfortunately we have to hide that to stop the
-- builtin machinery spotting it and then we have to re-abstract here.
-- | We could re-use the AbelianGroup class here, but that uses <> and `mempty`
-- and that's kind of confusing.
class (Eq a, Show a) => TestableAbelianGroup a
    where
      gname      :: String
      zero       :: a
      add        :: a -> a -> a
      neg        :: a -> a
      mul        :: Integer -> a -> a
      genElement :: Gen a
      zeroP      :: PlcTerm
      negP       :: PlcTerm -> PlcTerm
      addP       :: PlcTerm -> PlcTerm -> PlcTerm
      eqP        :: PlcTerm -> PlcTerm -> PlcTerm
      mulP       :: PlcTerm -> PlcTerm -> PlcTerm
      toPlc      :: a -> PlcTerm

class (Show e, TestableAbelianGroup a) => HashAndCompress e a
    where
      hashTo         :: ByteString -> a
      compress       :: a -> ByteString
      uncompress     :: ByteString -> Either e a
      compressedSize :: Integer
      compressP      :: PlcTerm -> PlcTerm
      uncompressP    :: PlcTerm -> PlcTerm
      hashToCurveP   :: PlcTerm -> PlcTerm

instance TestableAbelianGroup G1.Element
    where
      gname      = "G1"
      zero       = G1.zero
      add        = G1.add
      neg        = G1.neg
      mul        = G1.mul
      genElement = genG1element
      zeroP      = mkApp1 Bls12_381_G1_uncompress $ bytestring $ pack (0xc0 : replicate 47 0x00)
      negP       = mkApp1 Bls12_381_G1_neg
      addP       = mkApp2 Bls12_381_G1_add
      eqP        = mkApp2 Bls12_381_G1_equal
      mulP       = mkApp2 Bls12_381_G1_mul
      toPlc      = mkConstant ()

instance HashAndCompress BLSTError G1.Element
    where
      hashTo         = G1.hashToCurve
      compress       = G1.compress
      uncompress     = G1.uncompress
      compressedSize = 48
      compressP      = mkApp1 Bls12_381_G1_compress
      uncompressP    = mkApp1 Bls12_381_G1_uncompress
      hashToCurveP   = mkApp1 Bls12_381_G1_hashToCurve

instance TestableAbelianGroup G2.Element
    where
      gname      = "G2"
      zero       = G2.zero
      add        = G2.add
      neg        = G2.neg
      mul        = G2.mul
      genElement = genG2element
      zeroP      = mkApp1 Bls12_381_G2_uncompress $ bytestring $ pack (0xc0 : replicate 95 0x00)
      negP       = mkApp1 Bls12_381_G2_neg
      addP       = mkApp2 Bls12_381_G2_add
      eqP        = mkApp2 Bls12_381_G2_equal
      mulP       = mkApp2 Bls12_381_G2_mul
      toPlc      = mkConstant ()

instance HashAndCompress BLSTError G2.Element
    where
      hashTo         = G2.hashToCurve
      compress       = G2.compress
      uncompress     = G2.uncompress
      compressedSize = 48
      compressP      = mkApp1 Bls12_381_G2_compress
      uncompressP    = mkApp1 Bls12_381_G2_uncompress
      hashToCurveP   = mkApp1 Bls12_381_G2_hashToCurve

-- Hedgehog generators etc.

withNTests :: Property -> Property
withNTests = withTests 500

genByteString100 :: Gen ByteString
genByteString100 = Gen.bytes $ Range.linear 0 100

genByteString :: Gen ByteString
genByteString = Gen.bytes $ Range.linear 0 1000

genG1element :: Gen G1.Element
genG1element = G1.hashToCurve <$> Gen.bytes (Range.linear 0 64)

{-
ok :: Either BLSTError G1.Element -> Bool
ok (Right _) = True
ok _         = False

getValue :: Either BLSTError G1.Element -> G1.Element
getValue (Right s) = s
getValue _         = error "Unexpected thing"

normalise :: ByteString -> ByteString
normalise b =
    BS.pack $ reverse $ case reverse $ BS.unpack b of
             []        -> []
             _:_:_:_:t -> 0x00 : 0x00 : 0x00 : 0x00 : t

             -- 0x8 -> 1000
             -- 0x9 -> 1001
             -- 0xa -> 1010
             -- 0xb -> 1011
-}

fromR :: Either a b -> b
fromR (Right a) = a
fromR (Left _)  = error "Got Left, Right expected"

-- | Only about 25% of bytestrings will get through the filter
genG1element' :: Gen G1.Element
genG1element' = fromR <$> (Gen.filter isRight $ (G1.uncompress <$> Gen.bytes (Range.singleton 48)))

genG2element :: Gen G2.Element
genG2element = G2.hashToCurve <$> Gen.bytes (Range.linear 0 64)

genSmallScalar :: Gen Integer
genSmallScalar = Gen.integral $ Range.linear (-100) 100

genScalar :: Gen Integer
genScalar = Gen.integral $ Range.linear (-10000) 10000

-- PLC utilities

type PlcTerm = PLC.Term TyName Name DefaultUni DefaultFun ()
type UplcTerm = UPLC.Term Name DefaultUni DefaultFun ()

uplcTrue :: Maybe UplcTerm
uplcTrue = Just $ mkConstant () True

uplcFalse :: Maybe UplcTerm
uplcFalse = Just $ mkConstant () False

integer :: Integer -> PlcTerm
integer = mkConstant ()

bytestring :: ByteString -> PlcTerm
bytestring = mkConstant ()

mkApp1 :: DefaultFun -> PlcTerm -> PlcTerm
mkApp1 b x = mkIterApp () (builtin () b) [x]

mkApp2 :: DefaultFun -> PlcTerm -> PlcTerm -> PlcTerm
mkApp2 b x y = mkIterApp () (builtin () b) [x,y]

-- Constructing pairing terms

pairingPlc :: PlcTerm -> PlcTerm -> PlcTerm
pairingPlc = mkApp2 Bls12_381_GT_pairing

finalVerifyPlc :: PlcTerm -> PlcTerm -> PlcTerm
finalVerifyPlc = mkApp2 Bls12_381_GT_finalVerify

mulGT :: PlcTerm -> PlcTerm -> PlcTerm
mulGT = mkApp2 Bls12_381_GT_mul

-- Evaluating PLC terms

evalTerm
    :: PLC.Term TyName Name DefaultUni DefaultFun ()
    -> Maybe (UPLC.Term Name DefaultUni DefaultFun ())
evalTerm term =
    case typecheckEvaluateCekNoEmit DefaultFunV1 defaultBuiltinCostModel term
    of Left _ -> Nothing
       Right x  ->
           case x of
             EvaluationFailure   -> Nothing
             EvaluationSuccess s -> Just s


