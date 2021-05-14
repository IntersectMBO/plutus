{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

module Spec.Interval where

import           Data.List                 (sort)
import           Hedgehog                  (Property, forAll, property)
import qualified Hedgehog
import qualified Hedgehog.Gen              as Gen
import qualified Hedgehog.Range            as Range
import qualified Plutus.V1.Ledger.Interval as Interval
import           Plutus.V1.Ledger.Slot
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.Hedgehog       (testProperty)

alwaysIsNotEmpty :: TestTree
alwaysIsNotEmpty =
  testCase "always is not empty" $
    assertBool "always" (not $ Interval.isEmpty (Interval.always :: Interval.Interval Slot))

neverIsEmpty :: TestTree
neverIsEmpty =
  testCase "never is empty" $
    assertBool "never" (Interval.isEmpty (Interval.never :: Interval.Interval Slot))

intvlIsEmpty :: Property
intvlIsEmpty = property $ do
  (i1, i2) <- forAll $ (,) <$> Gen.integral (fromIntegral <$> Range.linearBounded @Int) <*> Gen.integral (fromIntegral <$> Range.linearBounded @Int)
  let (from, to) = (min i1 i2, max i1 i2)
      nonEmpty = Interval.interval (Slot from) (Slot to)
      empty = Interval.interval (Slot to) (Slot from)
  Hedgehog.assert $ from == to || Interval.isEmpty empty
  Hedgehog.assert $ not $ Interval.isEmpty nonEmpty

intvlIntersection :: Property
intvlIntersection = property $ do
  ints <- forAll $ traverse (const $ Gen.integral (fromIntegral <$> Range.linearBounded @Int)) [1..4 :: Integer]
  let [i1, i2, i3, i4] = Slot <$> sort ints
      outer = Interval.interval i1 i4
      inner = Interval.interval i2 i3
      intersec = outer `Interval.intersection` inner

      lower = Interval.interval i1 i2
      higher = Interval.interval i2 i3
      common = Interval.interval i2 i2
      intersec2 = lower `Interval.intersection` higher

  Hedgehog.assert $ intersec == inner
  Hedgehog.assert $ intersec2 == common

intvlIntersectionWithAlwaysNever :: Property
intvlIntersectionWithAlwaysNever = property $ do
  (i1, i2) <- forAll $ (,) <$> Gen.integral (fromIntegral <$> Range.linearBounded @Int) <*> Gen.integral (fromIntegral <$> Range.linearBounded @Int)
  let (from, to) = (min i1 i2, max i1 i2)
      i = Interval.interval (Slot from) (Slot to)
      e = Interval.interval (Slot to) (Slot from)

  Hedgehog.assert $ Interval.never == i `Interval.intersection` Interval.never
  Hedgehog.assert $ i == i `Interval.intersection` Interval.always
  Hedgehog.assert $ e == e `Interval.intersection` i

intvlOverlaps :: Property
intvlOverlaps = property $ do
  (i1, i2) <- forAll $ (,) <$> Gen.integral (fromIntegral <$> Range.linearBounded @Int) <*> Gen.integral (fromIntegral <$> Range.linearBounded @Int)
  let (from, to) = (min i1 i2, max i1 i2)
      i = Interval.interval (Slot from) (Slot to)

  Hedgehog.assert $ i `Interval.overlaps` i
  Hedgehog.assert $ Interval.always `Interval.overlaps` i
  Hedgehog.assert $ not $ Interval.never `Interval.overlaps` i

tests :: TestTree
tests =
  testGroup
    "plutus-ledger-api-interval"
    [ neverIsEmpty
    , alwaysIsNotEmpty
    , testProperty "interval intersection" intvlIntersection
    , testProperty "interval intersection with always/never" intvlIntersectionWithAlwaysNever
    , testProperty "interval isEmpty" intvlIsEmpty
    , testProperty "interval overlaps" intvlOverlaps
    ]
