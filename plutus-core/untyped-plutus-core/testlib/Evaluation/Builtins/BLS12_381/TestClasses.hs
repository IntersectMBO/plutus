{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Evaluation.Builtins.BLS12_381.TestClasses
where

import Evaluation.Builtins.Common (PlcTerm, mkApp1, mkApp2)

import PlutusCore.Crypto.BLS12_381.G1 qualified as G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as G2
import PlutusCore.Default
import PlutusCore.Generators.QuickCheck.Builtin (ArbitraryBuiltin)
import PlutusCore.MkPlc (mkConstant)

import Data.ByteString as BS (ByteString, empty)
import Test.QuickCheck (Arbitrary (..), Gen, frequency, suchThat)

---------------- Typeclasses for groups ----------------

{- | The code for the property tests for G1 and G2 is essentially identical, so
 it's worth abstracting over the common features.  The blst Haskell FFI uses a
 phantom type to do this but unfortunately we have to hide that to stop the
 builtin machinery spotting it and then we have to re-abstract here. -}

-- We could re-use the AbelianGroup class here, but that uses <> and `mempty`
-- and that's confusing.
class (Eq a, Show a, Arbitrary a, ArbitraryBuiltin a, DefaultUni `Contains` a) => TestableAbelianGroup a
    where
      groupName          :: String
      zero               :: a
      addTerm            :: PlcTerm -> PlcTerm -> PlcTerm
      negTerm            :: PlcTerm -> PlcTerm
      scalarMulTerm      :: PlcTerm -> PlcTerm -> PlcTerm
      multiScalarMulTerm :: PlcTerm -> PlcTerm -> PlcTerm
      eqTerm             :: PlcTerm -> PlcTerm -> PlcTerm

zeroTerm :: forall g. TestableAbelianGroup g => PlcTerm
zeroTerm = mkConstant () $ zero @g

-- An arbitrary nonzero group element.  For the BLS12-381 groups it's highly
-- unlikely that we'll get the zero element, but let's make sure.
arbitraryNonZero :: forall g. TestableAbelianGroup g => Gen g
arbitraryNonZero = (arbitrary @g) `suchThat` ((/=) (zero @g))

class TestableAbelianGroup a => HashAndCompress a
    where
      compressedSize  :: Int
      compress        :: a -> ByteString
      compressTerm    :: PlcTerm -> PlcTerm
      uncompressTerm  :: PlcTerm -> PlcTerm
      hashToGroupTerm :: PlcTerm -> PlcTerm -> PlcTerm

---------- Instances for G1 ----------

{- | Generate an arbitrary element of G1.  It's tricky to construct such an
 element directly without using quite low-level operations on the curve
 because a random point on the curve is highly unlikely to be in the subgroup
 G1, but fortunately `hashToGroup` always produces an element of the subgroup,
 so we can produce random elements of G1 by hashing random bytestrings. -}
instance Arbitrary G1.Element
    where
      arbitrary = frequency [ (9, arbitraryElement)
                            , (1, pure $ G1.offchain_zero)
                            ]
        where arbitraryElement =
                G1.hashToGroup <$> arbitrary <*> pure BS.empty >>= \case
                Left err -> error $ "Arbitrary instance for G1.Element:" ++ show err
                Right p  -> pure p

instance TestableAbelianGroup G1.Element
    where
      groupName          = "G1"
      zero               = G1.offchain_zero
      addTerm            = mkApp2 Bls12_381_G1_add
      negTerm            = mkApp1 Bls12_381_G1_neg
      scalarMulTerm      = mkApp2 Bls12_381_G1_scalarMul
      multiScalarMulTerm = mkApp2 Bls12_381_G1_multiScalarMul
      eqTerm             = mkApp2 Bls12_381_G1_equal

instance HashAndCompress G1.Element
    where
      compressedSize  = 48
      compress        = G1.compress
      compressTerm    = mkApp1 Bls12_381_G1_compress
      uncompressTerm  = mkApp1 Bls12_381_G1_uncompress
      hashToGroupTerm = mkApp2 Bls12_381_G1_hashToGroup

---------- Instances for G2 ----------

-- | See the comment for the Arbitrary instance for G1.
instance Arbitrary G2.Element
    where
      arbitrary = frequency [ (9, arbitraryElement)
                            , (1, pure $ G2.offchain_zero)
                            ]
        where arbitraryElement =
                G2.hashToGroup <$> arbitrary <*> pure BS.empty >>= \case
                Left err -> error $ "Arbitrary instance for G2.Element:" ++ show err
                Right p  -> pure p

instance TestableAbelianGroup G2.Element
    where
      groupName          = "G2"
      zero               = G2.offchain_zero
      addTerm            = mkApp2 Bls12_381_G2_add
      negTerm            = mkApp1 Bls12_381_G2_neg
      scalarMulTerm      = mkApp2 Bls12_381_G2_scalarMul
      multiScalarMulTerm = mkApp2 Bls12_381_G2_multiScalarMul
      eqTerm             = mkApp2 Bls12_381_G2_equal

instance HashAndCompress G2.Element
    where
      compressedSize  = 96
      compress        = G2.compress
      compressTerm    = mkApp1 Bls12_381_G2_compress
      uncompressTerm  = mkApp1 Bls12_381_G2_uncompress
      hashToGroupTerm = mkApp2 Bls12_381_G2_hashToGroup
