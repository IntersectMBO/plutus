{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE ViewPatterns      #-}

module Value.Spec (tests) where

import Data.ByteString (ByteString)
import Data.ByteString.Char8 qualified as BC
import Data.Foldable
import Data.Int
import Data.Map.Strict qualified as Map
import Data.Maybe
import Hedgehog (Gen, MonadTest, Property, assert, forAll, property, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusCore.Value (Value)
import PlutusCore.Value qualified as V
import Safe.Foldable (maximumMay)
import Test.Tasty
import Test.Tasty.Hedgehog

genCurrency :: Gen ByteString
genCurrency = Gen.element $ fmap (\(n :: Int) -> "currency" <> BC.pack (show n)) [1 .. 100]

genToken :: Gen ByteString
genToken = Gen.element $ fmap (\(n :: Int) -> "token" <> BC.pack (show n)) [1 .. 100]

genAmount :: Gen Integer
genAmount = toInteger @Int16 <$> Gen.enumBounded

genValue :: Gen Value
genValue = do
  n <- Gen.int (Range.constant 0 100)
  let f :: Int -> Value -> Gen Value
      f _ v = V.insertCoin <$> genCurrency <*> genToken <*> genAmount <*> pure v
  foldrM f V.empty [1 .. n]

genNestedMap :: Gen V.NestedMap
genNestedMap = do
  n <- Gen.int (Range.constant 0 100)
  let f :: Int -> V.NestedMap -> Gen V.NestedMap
      f _ nm = do
        currency <- genCurrency
        token <- genToken
        amt <- genAmount
        pure $ Map.insertWith (Map.unionWith (+)) currency (Map.singleton token amt) nm
  foldrM f mempty [1 .. n]

prop_packUnpackRoundtrip :: Property
prop_packUnpackRoundtrip = property $ do
  v <- forAll genValue
  v === V.pack (V.unpack v)

-- | Verifies that @pack@ correctly updates the sizes
prop_packBookkeeping :: Property
prop_packBookkeeping = property $ do
  nm <- forAll genNestedMap
  checkSizes (V.pack nm)

{-| Verifies that @pack@ preserves @Value@ invariants, i.e.,
no empty inner map or zero amount.
-}
prop_packPreservesInvariants :: Property
prop_packPreservesInvariants = property $ do
  nm <- forAll genNestedMap
  checkInvariants (V.pack nm)

-- | Verifies that @insertCoin@ correctly updates the sizes
prop_insertCoinBookkeeping :: Property
prop_insertCoinBookkeeping = property $ do
  v <- forAll genValue
  currency <- forAll genCurrency
  token <- forAll genToken
  amt <- forAll genAmount
  let v' = V.insertCoin currency token amt v
  checkSizes v'

-- | Verifies that @insertCoin@ preserves @Value@ invariants
prop_insertCoinPreservesInvariants :: Property
prop_insertCoinPreservesInvariants = property $ do
  v <- forAll genValue
  currency <- forAll genCurrency
  token <- forAll genToken
  amt <- forAll genAmount
  let v' = V.insertCoin currency token amt v
  checkInvariants v'

prop_unionCommutative :: Property
prop_unionCommutative = property $ do
  v <- forAll genValue
  v' <- forAll genValue
  V.unionValue v v' === V.unionValue v' v

prop_insertCoinIdempotent :: Property
prop_insertCoinIdempotent = property $ do
  v <- forAll genValue
  let fm = toFlatMap v
  v === foldl' (\acc (c, t, a) -> V.insertCoin c t a acc) v fm

checkSizes :: (MonadTest m) => Value -> m ()
checkSizes v =
  (expectedMaxInnerSize === actualMaxInnerSize)
    >> (expectedSize === actualSize)
 where
  expectedMaxInnerSize = fromMaybe 0 . maximumMay $ Map.map Map.size (V.unpack v)
  actualMaxInnerSize = V.maxInnerSize v
  expectedSize = sum $ Map.map Map.size (V.unpack v)
  actualSize = V.totalSize v

checkInvariants :: (MonadTest m) => Value -> m ()
checkInvariants (V.unpack -> v) = do
  assert $ (not . any Map.null) v
  assert $ (not . any (elem 0)) v

toFlatMap :: Value -> [(ByteString, ByteString, Integer)]
toFlatMap (V.toList -> xs) = [(c, t, a) | (c, ys) <- xs, (t, a) <- ys]

tests :: TestTree
tests =
  testGroup
    "Value"
    [ testPropertyNamed
        "packUnpackRoundtrip"
        "prop_packUnpackRoundtrip"
        prop_packUnpackRoundtrip
    , testPropertyNamed
        "packBookkeeping"
        "prop_packBookkeeping"
        prop_packBookkeeping
    , testPropertyNamed
        "packPreservesInvariants"
        "prop_packPreservesInvariants"
        prop_packPreservesInvariants
    , testPropertyNamed
        "insertCoinBookkeeping"
        "prop_insertCoinBookkeeping"
        prop_insertCoinBookkeeping
    , testPropertyNamed
        "insertCoinPreservesInvariants"
        "prop_insertCoinPreservesInvariants"
        prop_insertCoinPreservesInvariants
    , testPropertyNamed
        "unionCommutative"
        "prop_unionCommutative"
        prop_unionCommutative
    , testPropertyNamed
        "insertCoinIdempotent"
        "prop_insertCoinIdempotent"
        prop_insertCoinIdempotent
    ]
