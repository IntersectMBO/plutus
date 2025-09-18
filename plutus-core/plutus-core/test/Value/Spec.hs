{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Value.Spec (tests) where

import Data.Foldable qualified as F
import Data.Map.Strict qualified as Map
import Data.Maybe
import PlutusCore.Generators.QuickCheck.Builtin (arbitraryBuiltin, genShortHex)
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
prop_insertCoinBookkeeping = forAll arbitrary $ \v ->
  forAll (genShortHex (V.totalSize v)) $ \currency ->
    forAll (genShortHex (V.totalSize v)) $ \token ->
      forAll arbitraryBuiltin $ \amt ->
        let v' = V.insertCoin currency token amt v
         in checkSizes v'

-- | Verifies that @insertCoin@ preserves @Value@ invariants
prop_insertCoinPreservesInvariants :: Property
prop_insertCoinPreservesInvariants = forAll arbitrary $ \v ->
  forAll (genShortHex (V.totalSize v)) $ \currency ->
    forAll (genShortHex (V.totalSize v)) $ \token ->
      forAll arbitraryBuiltin $ \amt ->
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
   in v === F.foldl' (\acc (c, t, a) -> V.insertCoin c t a acc) v fm

prop_lookupAfterInsertion :: Property
prop_lookupAfterInsertion = forAll arbitrary $ \v ->
  forAll (genShortHex (V.totalSize v)) $ \currency ->
    forAll (genShortHex (V.totalSize v)) $ \token ->
      forAll arbitraryBuiltin $ \amt ->
        let v' = V.insertCoin currency token amt v
         in V.lookupCoin currency token v' === amt

prop_lookupAfterDeletion :: Property
prop_lookupAfterDeletion = forAll arbitrary $ \v ->
  forAll (genShortHex (V.totalSize v)) $ \currency ->
    forAll (genShortHex (V.totalSize v)) $ \token ->
      let v' = V.deleteCoin currency token v
       in V.lookupCoin currency token v' === 0

prop_deleteCoinIdempotent :: Property
prop_deleteCoinIdempotent = forAll (arbitrary `suchThat` (\v -> V.totalSize v > 0)) $ \v ->
  let fl = V.toFlatList v
   in forAll (elements fl) $ \(c, t, _) ->
        let v' = V.deleteCoin c t v
         in v' === V.deleteCoin c t v'

prop_containsReflexive :: Property
prop_containsReflexive = forAll arbitrary $ \v ->
  property $ V.valueContains v v

prop_containsAfterDeletion :: Property
prop_containsAfterDeletion = forAll arbitrary $ \v ->
  let fl = V.toFlatList v
      vs = scanr (\(c, t, _) -> V.deleteCoin c t) v fl
   in conjoin [property (V.valueContains v v') | v' <- vs]

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
