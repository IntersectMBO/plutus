{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Value.Spec (tests) where

import Data.Foldable
import Data.Map.Strict qualified as Map
import Data.Maybe
import PlutusCore.Generators.QuickCheck.Builtin ()
import PlutusCore.Generators.QuickCheck.Value (genShortHex)
import PlutusCore.Value (Value)
import PlutusCore.Value qualified as V
import Safe.Foldable (maximumMay)
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck

prop_packUnpackRoundtrip :: Property
prop_packUnpackRoundtrip = forAll arbitrary $ \v ->
  v === V.pack (V.unpack v)

-- | Verifies that @pack@ correctly updates the sizes
prop_packBookkeeping :: Property
prop_packBookkeeping = forAll arbitrary $ \nm ->
  checkSizes (V.pack nm)

{-| Verifies that @pack@ preserves @Value@ invariants, i.e.,
no empty inner map or zero amount.
-}
prop_packPreservesInvariants :: Property
prop_packPreservesInvariants = forAll arbitrary $ \nm ->
  checkInvariants (V.pack nm)

-- | Verifies that @insertCoin@ correctly updates the sizes
prop_insertCoinBookkeeping :: Property
prop_insertCoinBookkeeping = forAll arbitrary $ \(v, amt) ->
  forAll (genShortHex (V.totalSize v)) $ \currency ->
    forAll (genShortHex (V.totalSize v)) $ \token ->
      let v' = V.insertCoin currency token amt v
       in checkSizes v'

-- | Verifies that @insertCoin@ preserves @Value@ invariants
prop_insertCoinPreservesInvariants :: Property
prop_insertCoinPreservesInvariants = forAll arbitrary $ \(v, amt) ->
  forAll (genShortHex (V.totalSize v)) $ \currency ->
    forAll (genShortHex (V.totalSize v)) $ \token ->
      let v' = V.insertCoin currency token amt v
       in checkInvariants v'

prop_unionCommutative :: Property
prop_unionCommutative = forAll arbitrary $ \(v, v') ->
  V.unionValue v v' === V.unionValue v' v

prop_unionAssociative :: Property
prop_unionAssociative = forAll arbitrary $ \(v1, v2, v3) ->
  V.unionValue v1 (V.unionValue v2 v3) === V.unionValue (V.unionValue v1 v2) v3

prop_insertCoinIdempotent :: Property
prop_insertCoinIdempotent = forAll arbitrary $ \v ->
  let fm = V.toFlatList v
   in v === foldl' (\acc (c, t, a) -> V.insertCoin c t a acc) v fm

checkSizes :: Value -> Property
checkSizes v =
  (expectedMaxInnerSize === actualMaxInnerSize)
    .&&. (expectedSize === actualSize)
 where
  expectedMaxInnerSize = fromMaybe 0 . maximumMay $ Map.map Map.size (V.unpack v)
  actualMaxInnerSize = V.maxInnerSize v
  expectedSize = sum $ Map.map Map.size (V.unpack v)
  actualSize = V.totalSize v

checkInvariants :: Value -> Property
checkInvariants (V.unpack -> v) =
  property ((not . any Map.null) v)
    .&&. property ((not . any (elem 0)) v)

tests :: TestTree
tests =
  testGroup
    "Value"
    [ testProperty
        "packUnpackRoundtrip"
        prop_packUnpackRoundtrip
    , testProperty
        "packBookkeeping"
        prop_packBookkeeping
    , testProperty
        "packPreservesInvariants"
        prop_packPreservesInvariants
    , testProperty
        "insertCoinBookkeeping"
        prop_insertCoinBookkeeping
    , testProperty
        "insertCoinPreservesInvariants"
        prop_insertCoinPreservesInvariants
    , testProperty
        "unionCommutative"
        prop_unionCommutative
    , testProperty
        "unionAssociative"
        prop_unionAssociative
    , testProperty
        "insertCoinIdempotent"
        prop_insertCoinIdempotent
    ]
