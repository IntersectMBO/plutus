{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Value.Spec (tests) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as B
import Data.Either
import Data.Foldable qualified as F
import Data.Map.Strict qualified as Map
import Data.Maybe
import Safe.Foldable (maximumMay)
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck

import PlutusCore.Builtin (BuiltinResult (..))
import PlutusCore.Data (Data (..))
import PlutusCore.Flat qualified as Flat
import PlutusCore.Generators.QuickCheck.Builtin (ValueAmount (..), genShortHex)
import PlutusCore.Value (Value)
import PlutusCore.Value qualified as V

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
      let BuiltinSuccess v' = V.insertCoin (V.unK currency) (V.unK token) amt v
       in checkSizes v'

-- | Verifies that @insertCoin@ preserves @Value@ invariants
prop_insertCoinPreservesInvariants :: Value -> ValueAmount -> Property
prop_insertCoinPreservesInvariants v (ValueAmount amt) =
  forAll (genShortHex (V.totalSize v)) $ \currency ->
    forAll (genShortHex (V.totalSize v)) $ \token ->
      let BuiltinSuccess v' = V.insertCoin (V.unK currency) (V.unK token) amt v
       in checkInvariants v'

prop_unionCommutative :: Value -> Value -> Property
prop_unionCommutative v v' = V.unionValue v v' === V.unionValue v' v

prop_unionAssociative :: Value -> Value -> Value -> Property
prop_unionAssociative v1 v2 v3 =
  V.unionValue v1 (V.unionValue v2 v3) === V.unionValue (V.unionValue v1 v2) v3

prop_insertCoinIdempotent :: Value -> Property
prop_insertCoinIdempotent v =
  v
    === F.foldl'
      (\acc (c, t, a) -> let BuiltinSuccess v' = V.insertCoin (V.unK c) (V.unK t) a acc in v')
      v
      (V.toFlatList v)

prop_insertCoinValidatesCurrency :: Value -> Property
prop_insertCoinValidatesCurrency v =
  forAll gen33Bytes $ \c ->
    forAll gen32BytesOrFewer $ \t ->
      forAll (arbitrary `suchThat` (/= 0)) $ \amt ->
        case V.insertCoin c t amt v of
          BuiltinFailure{} -> property True
          _                -> property False

prop_insertCoinValidatesToken :: Value -> Property
prop_insertCoinValidatesToken v =
  forAll gen32BytesOrFewer $ \c ->
    forAll gen33Bytes $ \t ->
      forAll (arbitrary `suchThat` (/= 0)) $ \amt ->
        case V.insertCoin c t amt v of
          BuiltinFailure{} -> property True
          _                -> property False

prop_lookupAfterInsertion :: Value -> ValueAmount -> Property
prop_lookupAfterInsertion v (ValueAmount amt) =
  forAll (genShortHex (V.totalSize v)) $ \currency ->
    forAll (genShortHex (V.totalSize v)) $ \token ->
      let BuiltinSuccess v' = V.insertCoin (V.unK currency) (V.unK token) amt v
       in V.lookupCoin (V.unK currency) (V.unK token) v' === amt

prop_lookupAfterDeletion :: Value -> Property
prop_lookupAfterDeletion v =
  forAll (genShortHex (V.totalSize v)) $ \currency ->
    forAll (genShortHex (V.totalSize v)) $ \token ->
      let v' = V.deleteCoin (V.unK currency) (V.unK token) v
       in V.lookupCoin (V.unK currency) (V.unK token) v' === 0

prop_deleteCoinIdempotent :: Value -> Property
prop_deleteCoinIdempotent v0 =
  forAll (elements fl) $ \(V.unK -> c, V.unK -> t, _) ->
    let v' = V.deleteCoin c t v
     in v' === V.deleteCoin c t v'
 where
  BuiltinSuccess v = if V.totalSize v0 > 0 then pure v0 else V.insertCoin "c" "t" 1 v0
  fl = V.toFlatList v

prop_containsReflexive :: Value -> Property
prop_containsReflexive v = property $ V.valueContains v v

prop_containsAfterDeletion :: Value -> Property
prop_containsAfterDeletion v =
  conjoin [property (V.valueContains v v') | v' <- vs]
 where
  fl = V.toFlatList v
  vs = scanr (\(c, t, _) -> V.deleteCoin (V.unK c) (V.unK t)) v fl

prop_flatRoundtrip :: Value -> Property
prop_flatRoundtrip v = Flat.unflat (Flat.flat v) === Right v

gen32BytesOrFewer :: Gen ByteString
gen32BytesOrFewer = do
  len <- chooseInt (0, 32)
  B.pack <$> vectorOf len arbitrary

gen33Bytes :: Gen ByteString
gen33Bytes = B.pack <$> vectorOf 33 arbitrary

prop_flatDecodeSuccess :: Property
prop_flatDecodeSuccess = forAll (arbitrary `suchThat` (/= 0)) $ \amt ->
  forAll gen32BytesOrFewer $ \c ->
    forAll gen32BytesOrFewer $ \t ->
      let flat = Flat.flat $ Map.singleton c (Map.singleton t amt)
          BuiltinSuccess v = V.insertCoin c t amt V.empty
       in Flat.unflat flat === Right v

prop_flatDecodeInvalidCurrency :: Property
prop_flatDecodeInvalidCurrency =
  forAll gen33Bytes $ \c ->
    forAll gen32BytesOrFewer $ \t ->
      let flat = Flat.flat $ Map.singleton c (Map.singleton t (100 :: Integer))
       in property . isLeft $ Flat.unflat @Value flat

prop_flatDecodeInvalidToken :: Property
prop_flatDecodeInvalidToken =
  forAll gen32BytesOrFewer $ \c ->
    forAll gen33Bytes $ \t ->
      let flat = Flat.flat $ Map.singleton c (Map.singleton t (100 :: Integer))
       in property . isLeft $ Flat.unflat @Value flat

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

prop_unValueDataValidatesCurrency :: ValueAmount -> Property
prop_unValueDataValidatesCurrency (ValueAmount amt) =
  forAll gen33Bytes $ \c ->
    forAll gen32BytesOrFewer $ \t ->
      let d = Map [(B c, Map [(B t, I amt)])]
       in case V.unValueData d of
            BuiltinFailure{} -> property True
            _                -> property False

prop_unValueDataValidatesToken :: ValueAmount -> Property
prop_unValueDataValidatesToken (ValueAmount amt) =
  forAll gen32BytesOrFewer $ \c ->
    forAll gen33Bytes $ \t ->
      let d = Map [(B c, Map [(B t, I amt)])]
       in case V.unValueData d of
            BuiltinFailure{} -> property True
            _                -> property False

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
        "insertCoinValidatesCurrency"
        prop_insertCoinValidatesCurrency
    , testProperty
        "insertCoinValidatesToken"
        prop_insertCoinValidatesToken
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
    , testProperty
        "unValueDataValidatesCurrency"
        prop_unValueDataValidatesCurrency
    , testProperty
        "unValueDataValidatesToken"
        prop_unValueDataValidatesToken
    , testProperty
        "flatRoundtrip"
        prop_flatRoundtrip
    , testProperty
        "flatDecodeSuccess"
        prop_flatDecodeSuccess
    , testProperty
        "flatDecodeInvalidCurrency"
        prop_flatDecodeInvalidCurrency
    , testProperty
        "flatDecodeInvalidToken"
        prop_flatDecodeInvalidToken
    ]
