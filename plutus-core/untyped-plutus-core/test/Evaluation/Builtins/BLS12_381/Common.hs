{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Evaluation.Builtins.BLS12_381.Common
where

import Evaluation.Builtins.Common
import PlutusCore.BLS12_381.G1 qualified as G1
import PlutusCore.BLS12_381.G2 qualified as G2

import Crypto.EllipticCurve.BLS12_381 (BLSTError)
import PlutusCore as PLC
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.MkPlc (builtin, mkConstant, mkIterApp)
import UntypedPlutusCore as UPLC

import PlutusCore.Generators.QuickCheck.Builtin
import Test.QuickCheck

import Data.ByteString as BS (ByteString, pack)
import Text.Printf (printf)


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
      mul        :: Integer -> a -> a
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
      compressedSize :: Int
      compressP      :: PlcTerm -> PlcTerm
      uncompressP    :: PlcTerm -> PlcTerm
      hashToCurveP   :: PlcTerm -> PlcTerm


-- | Generate an arbitrary element of G1.  It's tricky to construct such an
-- element directly without using quite low-level operations on the curve
-- because a random point on the curve is highly unlikely to be in the subgroup
-- G1, but fortunately `hashToCurve` always produces an element of the subgroup,
-- so we can produce random elements of G1 by hasing random bytestrings.
instance Arbitrary G1.Element
    where
      arbitrary = G1.hashToCurve <$> arbitrary

instance TestableAbelianGroup G1.Element
    where
      gname      = "G1"
      zero       = G1.zero
      add        = G1.add
      neg        = G1.neg
      mul        = G1.mul
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

-- | See the comment for the Arbitrary instance for G1.
instance Arbitrary G2.Element
    where
      arbitrary = G2.hashToCurve <$> arbitrary

instance TestableAbelianGroup G2.Element
    where
      gname      = "G2"
      zero       = G2.zero
      add        = G2.add
      neg        = G2.neg
      mul        = G2.mul
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

-- QuickCheck utilities

mkTestName :: forall a. TestableAbelianGroup a => String -> String
mkTestName s = printf "%s_%s" (gname @a) s

withNTests :: Testable prop => prop -> Property
withNTests = withMaxSuccess 200

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

pairingPlc :: PlcTerm -> PlcTerm -> PlcTerm
pairingPlc = mkApp2 Bls12_381_GT_pairing

finalVerifyPlc :: PlcTerm -> PlcTerm -> PlcTerm
finalVerifyPlc = mkApp2 Bls12_381_GT_finalVerify

mulGT :: PlcTerm -> PlcTerm -> PlcTerm
mulGT = mkApp2 Bls12_381_GT_mul

