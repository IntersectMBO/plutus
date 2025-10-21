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
import PlutusCore.Generators.QuickCheck.Builtin (arbitraryBuiltin, genShortHex)
import PlutusCore.Value (Value)
import PlutusCore.Value qualified as V

prop_packUnpackRoundtrip :: Value -> Property
prop_packUnpackRoundtrip v = v === V.pack (V.unpack v)

-- | Verifies that @pack@ correctly updates the sizes
prop_packBookkeeping :: V.NestedMap -> Property
prop_packBookkeeping = checkBookkeeping . V.pack

{-| Verifies that @pack@ preserves @Value@ invariants, i.e.,
no empty inner map or zero amount.
-}
prop_packPreservesInvariants :: V.NestedMap -> Property
prop_packPreservesInvariants = checkInvariants . V.pack

-- | Verifies that @insertCoin@ correctly updates the sizes
prop_insertCoinBookkeeping :: Value -> V.Quantity -> Property
prop_insertCoinBookkeeping v quantity =
  forAll (genShortHex (V.totalSize v)) $ \currency ->
    forAll (genShortHex (V.totalSize v)) $ \token ->
      let BuiltinSuccess v' =
            V.insertCoin (V.unK currency) (V.unK token) (V.unQuantity quantity) v
       in checkBookkeeping v'

-- | Verifies that @insertCoin@ preserves @Value@ invariants
prop_insertCoinPreservesInvariants :: Value -> V.Quantity -> Property
prop_insertCoinPreservesInvariants v quantity =
  forAll (genShortHex (V.totalSize v)) $ \currency ->
    forAll (genShortHex (V.totalSize v)) $ \token ->
      let BuiltinSuccess v' =
            V.insertCoin (V.unK currency) (V.unK token) (V.unQuantity quantity) v
       in checkInvariants v'

prop_unionCommutative :: Value -> Value -> Property
prop_unionCommutative v v' =
  case (V.unionValue v v', V.unionValue v' v) of
    (BuiltinSuccess r1, BuiltinSuccess r2) -> r1 === r2
    (BuiltinFailure{}, BuiltinFailure{})   -> property True
    _                                      -> property False

prop_unionAssociative :: Value -> Value -> Value -> Property
prop_unionAssociative v1 v2 v3 =
  let succeeded = not . null
      extractValue = foldr const (error "extractValue called on BuiltinFailure")

      r23 = V.unionValue v2 v3
      r12 = V.unionValue v1 v2
   in if succeeded r23 && succeeded r12
        then do
          let r1 = V.unionValue v1 (extractValue r23)
              r2 = V.unionValue (extractValue r12) v3
          if succeeded r1 && succeeded r2
            then extractValue r1 === extractValue r2
            else discard
        else discard

prop_insertCoinIdempotent :: Value -> Property
prop_insertCoinIdempotent v =
  v
    === F.foldl'
      (\acc (c, t, q) ->
        let BuiltinSuccess v' = V.insertCoin (V.unK c) (V.unK t) (V.unQuantity q) acc
         in v')
      v
      (V.toFlatList v)

prop_insertCoinValidatesCurrency :: Value -> Property
prop_insertCoinValidatesCurrency v =
  forAll gen33Bytes $ \c ->
    forAll gen32BytesOrFewer $ \t ->
      forAll (arbitraryBuiltin `suchThat` (/= 0)) $ \quantity ->
        case V.insertCoin c t quantity v of
          BuiltinFailure{} -> property True
          _                -> property False

prop_insertCoinValidatesToken :: Value -> Property
prop_insertCoinValidatesToken v =
  forAll gen32BytesOrFewer $ \c ->
    forAll gen33Bytes $ \t ->
      forAll (arbitraryBuiltin `suchThat` (/= 0)) $ \quantity ->
        case V.insertCoin c t quantity v of
          BuiltinFailure{} -> property True
          _                -> property False

prop_insertCoinValidatesQuantityMin :: Value -> Property
prop_insertCoinValidatesQuantityMin v =
  forAll gen32BytesOrFewer $ \c ->
    forAll gen32BytesOrFewer $ \t ->
      forAll genBelowMinQuantity $ \quantity ->
        case V.insertCoin c t quantity v of
          BuiltinFailure{} -> property True
          _                -> property False

prop_insertCoinValidatesQuantityMax :: Value -> Property
prop_insertCoinValidatesQuantityMax v =
  forAll gen32BytesOrFewer $ \c ->
    forAll gen32BytesOrFewer $ \t ->
      forAll genAboveMaxQuantity $ \quantity ->
        case V.insertCoin c t quantity v of
          BuiltinFailure{} -> property True
          _                -> property False

prop_lookupAfterInsertion :: Value -> V.Quantity -> Property
prop_lookupAfterInsertion v quantity =
  forAll (genShortHex (V.totalSize v)) $ \currency ->
    forAll (genShortHex (V.totalSize v)) $ \token ->
      let BuiltinSuccess v' =
            V.insertCoin (V.unK currency) (V.unK token) (V.unQuantity quantity) v
       in V.lookupCoin (V.unK currency) (V.unK token) v' === V.unQuantity quantity

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

prop_deleteCoinBookkeeping :: Value -> Property
prop_deleteCoinBookkeeping v =
  conjoin [property (checkBookkeeping v') | v' <- vs]
 where
  fl = V.toFlatList v
  vs = scanr (\(c, t, _) -> V.deleteCoin (V.unK c) (V.unK t)) v fl

prop_deleteCoinPreservesInvariants :: Value -> Property
prop_deleteCoinPreservesInvariants v =
  conjoin [property (checkInvariants v') | v' <- vs]
 where
  fl = V.toFlatList v
  vs = scanr (\(c, t, _) -> V.deleteCoin (V.unK c) (V.unK t)) v fl

toPositiveValue :: Value -> Value
toPositiveValue =
  V.pack . fmap (Map.map (fromMaybe maxBound . V.quantity . abs . V.unQuantity)) . V.unpack

prop_containsReflexive :: Value -> Property
prop_containsReflexive (toPositiveValue -> v) =
  property $ case V.valueContains v v of
    BuiltinSuccess r -> r
    _                -> False

prop_containsAfterDeletion :: Value -> Property
prop_containsAfterDeletion (toPositiveValue -> v) =
  conjoin [property (case V.valueContains v v' of BuiltinSuccess r -> r; _ -> False) | v' <- vs]
 where
  fl = V.toFlatList v
  vs = scanr (\(c, t, _) -> V.deleteCoin (V.unK c) (V.unK t)) v fl

prop_containsEnforcesPositivity :: Value -> Property
prop_containsEnforcesPositivity v
  | V.negativeAmounts v == 0 = case (V.valueContains v V.empty, V.valueContains V.empty v) of
      (BuiltinSuccess{}, BuiltinSuccess{}) -> property True
      _                                    -> property False
  | otherwise = case (V.valueContains v V.empty, V.valueContains V.empty v) of
      (BuiltinFailure{}, BuiltinFailure{}) -> property True
      _                                    -> property False

prop_flatRoundtrip :: Value -> Property
prop_flatRoundtrip v = Flat.unflat (Flat.flat v) === Right v

gen32BytesOrFewer :: Gen ByteString
gen32BytesOrFewer = do
  len <- chooseInt (0, 32)
  B.pack <$> vectorOf len arbitrary

gen33Bytes :: Gen ByteString
gen33Bytes = B.pack <$> vectorOf 33 arbitrary

genBelowMinQuantity :: Gen Integer
genBelowMinQuantity = do
  Positive offset <- arbitrary
  pure (V.unQuantity minBound - offset)

genAboveMaxQuantity :: Gen Integer
genAboveMaxQuantity = do
  Positive offset <- arbitrary
  pure (V.unQuantity maxBound + offset)

prop_flatDecodeSuccess :: Property
prop_flatDecodeSuccess = forAll (arbitraryBuiltin `suchThat` (/= 0)) $ \quantity ->
  forAll gen32BytesOrFewer $ \c ->
    forAll gen32BytesOrFewer $ \t ->
      let flat = Flat.flat $ Map.singleton c (Map.singleton t quantity)
          BuiltinSuccess v = V.insertCoin c t quantity V.empty
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

checkBookkeeping :: Value -> Property
checkBookkeeping v =
  (expectedMaxInnerSize === actualMaxInnerSize)
    .&&. (expectedSize === actualSize)
    .&&. (expectedNeg === actualNeg)
 where
  expectedMaxInnerSize = fromMaybe 0 . maximumMay $ Map.map Map.size (V.unpack v)
  actualMaxInnerSize = V.maxInnerSize v
  expectedSize = sum $ Map.map Map.size (V.unpack v)
  actualSize = V.totalSize v
  expectedNeg =
    length [q | inner <- Map.elems (V.unpack v), q <- Map.elems inner, V.unQuantity q < 0]
  actualNeg = V.negativeAmounts v

checkInvariants :: Value -> Property
checkInvariants (V.unpack -> v) =
  property ((not . any Map.null) v)
    .&&. property ((not . any (elem V.zeroQuantity)) v)

prop_unValueDataValidatesCurrency :: V.Quantity -> Property
prop_unValueDataValidatesCurrency quantity =
  forAll gen33Bytes $ \c ->
    forAll gen32BytesOrFewer $ \t ->
      let d = Map [(B c, Map [(B t, I (V.unQuantity quantity))])]
       in case V.unValueData d of
            BuiltinFailure{} -> property True
            _                -> property False

prop_unValueDataValidatesToken :: V.Quantity -> Property
prop_unValueDataValidatesToken quantity =
  forAll gen32BytesOrFewer $ \c ->
    forAll gen33Bytes $ \t ->
      let d = Map [(B c, Map [(B t, I (V.unQuantity quantity))])]
       in case V.unValueData d of
            BuiltinFailure{} -> property True
            _                -> property False

prop_unValueDataValidatesQuantityMin :: Property
prop_unValueDataValidatesQuantityMin =
  forAll gen32BytesOrFewer $ \c ->
    forAll gen32BytesOrFewer $ \t ->
      forAll genBelowMinQuantity $ \quantity ->
        let d = Map [(B c, Map [(B t, I quantity)])]
         in case V.unValueData d of
              BuiltinFailure{} -> property True
              _                -> property False

prop_unValueDataValidatesQuantityMax :: Property
prop_unValueDataValidatesQuantityMax =
  forAll gen32BytesOrFewer $ \c ->
    forAll gen32BytesOrFewer $ \t ->
      forAll genAboveMaxQuantity $ \quantity ->
        let d = Map [(B c, Map [(B t, I quantity)])]
         in case V.unValueData d of
              BuiltinFailure{} -> property True
              _                -> property False

prop_unValueDataValidatesMixedQuantities :: Property
prop_unValueDataValidatesMixedQuantities =
  forAll genValueDataWithMixedQuantities $ \(dataVal, hasInvalid) ->
    case V.unValueData dataVal of
      BuiltinSuccess{}         -> not hasInvalid
      BuiltinSuccessWithLogs{} -> not hasInvalid
      BuiltinFailure{}         -> hasInvalid
 where
  -- Generate Value Data with mixed valid/invalid quantities (90% valid, 10% invalid)
  genValueDataWithMixedQuantities :: Gen (Data, Bool)
  genValueDataWithMixedQuantities = do
    numEntries <- chooseInt (1, 10)
    entries <- vectorOf numEntries $ do
      c <- gen32BytesOrFewer
      t <- gen32BytesOrFewer
      -- 90% valid, 10% invalid
      quantity <- frequency
        [ (9, arbitraryBuiltin :: Gen Integer)  -- valid range
        , (1, oneof [genBelowMinQuantity, genAboveMaxQuantity])  -- invalid
        ]
      pure (B c, Map [(B t, I quantity)])
    let hasInvalid = any (\(_, Map inner) -> any isInvalidQuantity inner) entries
        isInvalidQuantity (_, I q) = q < V.unQuantity minBound || q > V.unQuantity maxBound
        isInvalidQuantity _        = False
    pure (Map entries, hasInvalid)

prop_unionValueDetectsOverflow :: Property
prop_unionValueDetectsOverflow =
  forAll gen32BytesOrFewer $ \c ->
    forAll gen32BytesOrFewer $ \t ->
      let BuiltinSuccess v1 = V.insertCoin c t (V.unQuantity maxBound) V.empty
          BuiltinSuccess v2 = V.insertCoin c t 1 V.empty
       in case V.unionValue v1 v2 of
            BuiltinFailure{} -> property True
            _                -> property False

prop_flatDecodeInvalidQuantityMin :: Property
prop_flatDecodeInvalidQuantityMin =
  forAll gen32BytesOrFewer $ \c ->
    forAll gen32BytesOrFewer $ \t ->
      forAll genBelowMinQuantity $ \quantity ->
        let flat = Flat.flat $ Map.singleton c (Map.singleton t quantity)
         in property . isLeft $ Flat.unflat @Value flat

prop_flatDecodeInvalidQuantityMax :: Property
prop_flatDecodeInvalidQuantityMax =
  forAll gen32BytesOrFewer $ \c ->
    forAll gen32BytesOrFewer $ \t ->
      forAll genAboveMaxQuantity $ \quantity ->
        let flat = Flat.flat $ Map.singleton c (Map.singleton t quantity)
         in property . isLeft $ Flat.unflat @Value flat

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
        "insertCoinValidatesQuantityMin"
        prop_insertCoinValidatesQuantityMin
    , testProperty
        "insertCoinValidatesQuantityMax"
        prop_insertCoinValidatesQuantityMax
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
        "deleteCoinBookkeeping"
        prop_deleteCoinBookkeeping
    , testProperty
        "deleteCoinPreservesInvariants"
        prop_deleteCoinPreservesInvariants
    , testProperty
        "containsReflexive"
        prop_containsReflexive
    , testProperty
        "containsAfterDeletion"
        prop_containsAfterDeletion
    , testProperty
        "containsEnforcesPositivity"
        prop_containsEnforcesPositivity
    , testProperty
        "unValueDataValidatesCurrency"
        prop_unValueDataValidatesCurrency
    , testProperty
        "unValueDataValidatesToken"
        prop_unValueDataValidatesToken
    , testProperty
        "unValueDataValidatesQuantityMin"
        prop_unValueDataValidatesQuantityMin
    , testProperty
        "unValueDataValidatesQuantityMax"
        prop_unValueDataValidatesQuantityMax
    , testProperty
        "unValueDataValidatesMixedQuantities"
        prop_unValueDataValidatesMixedQuantities
    , testProperty
        "unionValueDetectsOverflow"
        prop_unionValueDetectsOverflow
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
    , testProperty
        "flatDecodeInvalidQuantityMin"
        prop_flatDecodeInvalidQuantityMin
    , testProperty
        "flatDecodeInvalidQuantityMax"
        prop_flatDecodeInvalidQuantityMax
    ]
