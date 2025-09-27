{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Value.Spec (tests) where

import Data.Foldable qualified as F
import Data.Map.Strict qualified as Map
import Data.Maybe
import PlutusCore.Generators.QuickCheck.Builtin (ValueAmount (..), genShortHex)
import PlutusCore.Value (Value)
import PlutusCore.Value qualified as V
import Safe.Foldable (maximumMay)
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck

prop_packUnpackRoundtrip :: Value -> Property
prop_packUnpackRoundtrip v = v === V.pack (V.unpack v)

-- | Verifies that @pack@ correctly updates the sizes
prop_packBookkeeping :: V.NestedMap -> Property
prop_packBookkeeping = checkSizes . V.pack

{-| Verifies that @pack@ preserves @Value@ invariants, i.e.,
no empty inner map or zero amount.
-}
prop_packPreservesInvariants :: V.NestedMap -> Property
prop_packPreservesInvariants = checkInvariants . V.pack

-- | Verifies that @insertCoin@ correctly updates the sizes
prop_insertCoinBookkeeping :: Value -> ValueAmount -> Property
prop_insertCoinBookkeeping v (ValueAmount amt) =
  forAll (genShortHex (V.totalSize v)) $ \currency ->
    forAll (genShortHex (V.totalSize v)) $ \token ->
      let v' = V.insertCoin currency token amt v
       in checkSizes v'

-- | Verifies that @insertCoin@ preserves @Value@ invariants
prop_insertCoinPreservesInvariants :: Value -> ValueAmount -> Property
prop_insertCoinPreservesInvariants v (ValueAmount amt) =
  forAll (genShortHex (V.totalSize v)) $ \currency ->
    forAll (genShortHex (V.totalSize v)) $ \token ->
      let v' = V.insertCoin currency token amt v
       in checkInvariants v'

prop_unionCommutative :: Value -> Value -> Property
prop_unionCommutative v v' = V.unionValue v v' === V.unionValue v' v

prop_unionAssociative :: Value -> Value -> Value -> Property
prop_unionAssociative v1 v2 v3 =
  V.unionValue v1 (V.unionValue v2 v3) === V.unionValue (V.unionValue v1 v2) v3

prop_insertCoinIdempotent :: Value -> Property
prop_insertCoinIdempotent v = v === F.foldl' (\acc (c, t, a) -> V.insertCoin c t a acc) v fm
 where
  fm = V.toFlatList v

prop_lookupAfterInsertion :: Value -> ValueAmount -> Property
prop_lookupAfterInsertion v (ValueAmount amt) =
  forAll (genShortHex (V.totalSize v)) $ \currency ->
    forAll (genShortHex (V.totalSize v)) $ \token ->
      let v' = V.insertCoin currency token amt v
       in V.lookupCoin currency token v' === amt

prop_lookupAfterDeletion :: Value -> Property
prop_lookupAfterDeletion v =
  forAll (genShortHex (V.totalSize v)) $ \currency ->
    forAll (genShortHex (V.totalSize v)) $ \token ->
      let v' = V.deleteCoin currency token v
       in V.lookupCoin currency token v' === 0

prop_deleteCoinIdempotent :: Value -> Property
prop_deleteCoinIdempotent v0 =
  forAll (elements fl) $ \(c, t, _) ->
    let v' = V.deleteCoin c t v
     in v' === V.deleteCoin c t v'
 where
  v = if V.totalSize v0 > 0 then v0 else V.insertCoin "c" "t" 1 v0
  fl = V.toFlatList v

prop_containsReflexive :: Value -> Property
prop_containsReflexive v = property $ V.valueContains v v

prop_containsAfterDeletion :: Value -> Property
prop_containsAfterDeletion v =
  conjoin [property (V.valueContains v v') | v' <- vs]
 where
  fl = V.toFlatList v
  vs = scanr (\(c, t, _) -> V.deleteCoin c t) v fl

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
    , testProperty
        "lookupAfterInsertion"
        prop_lookupAfterInsertion
    , testProperty
        "lookupAfterDeletion"
        prop_lookupAfterDeletion
    , testProperty
        "deleteCoinIdempotent"
        prop_deleteCoinIdempotent
    , testProperty
        "containsReflexive"
        prop_containsReflexive
    , testProperty
        "containsAfterDeletion"
        prop_containsAfterDeletion
    ]
