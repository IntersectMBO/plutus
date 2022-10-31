-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

module Spec.Interval where

import Data.List (sort)
import Hedgehog (Property, forAll, property)
import Hedgehog qualified
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusLedgerApi.V1.Interval qualified as Interval
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testPropertyNamed)
import Test.Tasty.HUnit (assertBool, testCase)

alwaysIsNotEmpty :: TestTree
alwaysIsNotEmpty =
  testCase "always is not empty" $
    assertBool "always" (not $ Interval.isEmpty (Interval.always :: Interval.Interval Integer))

neverIsEmpty :: TestTree
neverIsEmpty =
  testCase "never is empty" $
    assertBool "never" (Interval.isEmpty (Interval.never :: Interval.Interval Integer))

openIsEmpty :: TestTree
openIsEmpty =
  testCase "open interval isEmpty" $
    assertBool "open" (Interval.isEmpty (Interval.Interval (Interval.strictLowerBound 4) (Interval.strictUpperBound 5) :: Interval.Interval Integer))

openOverlaps :: TestTree
openOverlaps =
  testCase "open interval overlaps" $
    let a = Interval.Interval (Interval.strictLowerBound 1) (Interval.strictUpperBound 5) :: Interval.Interval Integer
        b = Interval.Interval (Interval.strictLowerBound 4) (Interval.strictUpperBound 6) :: Interval.Interval Integer
    in assertBool "overlaps" (not $ Interval.overlaps a b)

intvlIsEmpty :: Property
intvlIsEmpty = property $ do
  (i1, i2) <- forAll $ (,) <$> Gen.integral (toInteger <$> Range.linearBounded @Int) <*> Gen.integral (toInteger <$> Range.linearBounded @Int)
  let (from, to) = (min i1 i2, max i1 i2)
      nonEmpty = Interval.interval from to
      empty = Interval.interval to from
  Hedgehog.assert $ from == to || Interval.isEmpty empty
  Hedgehog.assert $ not $ Interval.isEmpty nonEmpty

intvlIntersection :: Property
intvlIntersection = property $ do
  ints <- forAll $ traverse (const $ Gen.integral (toInteger <$> Range.linearBounded @Int)) [1..4 :: Integer]
  let [i1, i2, i3, i4] = sort ints
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
  (i1, i2) <- forAll $ (,) <$> Gen.integral (toInteger <$> Range.linearBounded @Int) <*> Gen.integral (toInteger <$> Range.linearBounded @Int)
  let (from, to) = (min i1 i2, max i1 i2)
      i = Interval.interval from to
      e = Interval.interval to from

  Hedgehog.assert $ Interval.never == i `Interval.intersection` Interval.never
  Hedgehog.assert $ i == i `Interval.intersection` Interval.always
  Hedgehog.assert $ e == e `Interval.intersection` i

intvlOverlaps :: Property
intvlOverlaps = property $ do
  (i1, i2) <- forAll $ (,) <$> Gen.integral (toInteger <$> Range.linearBounded @Int) <*> Gen.integral (toInteger <$> Range.linearBounded @Int)
  let (from, to) = (min i1 i2, max i1 i2)
      i = Interval.interval from to

  Hedgehog.assert $ i `Interval.overlaps` i
  Hedgehog.assert $ Interval.always `Interval.overlaps` i
  Hedgehog.assert $ not $ Interval.never `Interval.overlaps` i

tests :: TestTree
tests =
  testGroup
    "plutus-ledger-api-interval"
    [ neverIsEmpty
    , alwaysIsNotEmpty
    , openIsEmpty
    , openOverlaps
    , testPropertyNamed "interval intersection" "intvIntersection" intvlIntersection
    , testPropertyNamed "interval intersection with always/never" "intvlIntersectionWithAlwaysNever" intvlIntersectionWithAlwaysNever
    , testPropertyNamed "interval isEmpty" "intvlIsEmpty" intvlIsEmpty
    , testPropertyNamed "interval overlaps" "intvlOverlaps" intvlOverlaps
    ]
