-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

module Spec.Interval where

import Data.List (sort)
import Data.Maybe (fromJust)
import Data.Set qualified as Set
import Hedgehog (Property, forAll, property)
import Hedgehog qualified
import Hedgehog.Gen qualified as Gen
import Hedgehog.Laws.Eq
import Hedgehog.Laws.Lattice
import Hedgehog.Laws.Ord
import Hedgehog.Range qualified as Range
import PlutusLedgerApi.V1.Interval qualified as Interval
import PlutusPrelude (reoption)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import Test.Tasty.HUnit (assertBool, testCase)

-- TODO: maybe bias towards generating non-empty intervals?

genExtended :: Bool -> Hedgehog.Gen a -> Hedgehog.Gen (Interval.Extended a)
genExtended finite g =
  if finite
  then Interval.Finite <$> g
  else Gen.choice [ Interval.Finite <$> g, pure Interval.NegInf, pure Interval.PosInf ]

genLowerBound :: Bool -> Hedgehog.Gen a -> Hedgehog.Gen (Interval.LowerBound a)
genLowerBound finite g = Interval.LowerBound <$> genExtended finite g <*> Gen.bool

genUpperBound :: Bool -> Hedgehog.Gen a -> Hedgehog.Gen (Interval.UpperBound a)
genUpperBound finite g = Interval.UpperBound <$> genExtended finite g <*> Gen.bool

genInterval :: Bool -> Hedgehog.Gen a -> Hedgehog.Gen (Interval.Interval a)
genInterval finite g = Interval.Interval <$> genLowerBound finite g <*> genUpperBound finite g

genFiniteDiscreteInterval :: Hedgehog.Gen (Interval.Interval Integer)
genFiniteDiscreteInterval = genInterval True (Gen.integral (toInteger <$> Range.linear @Int 0 100))

genDiscreteInterval :: Hedgehog.Gen (Interval.Interval Integer)
genDiscreteInterval = genInterval False (Gen.integral (toInteger <$> Range.linear @Int 0 100))

-- Unit tests

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

-- Property tests

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

intvlOverlaps :: Property
intvlOverlaps = property $ do
  (i1, i2) <- forAll $ (,) <$> Gen.integral (toInteger <$> Range.linearBounded @Int) <*> Gen.integral (toInteger <$> Range.linearBounded @Int)
  let (from, to) = (min i1 i2, max i1 i2)
      i = Interval.interval from to

  Hedgehog.assert $ i `Interval.overlaps` i
  Hedgehog.assert $ Interval.always `Interval.overlaps` i
  Hedgehog.assert $ not $ Interval.never `Interval.overlaps` i

{- Set model tests

We can give a semantic model for a finite (inded small), discrete interval in terms of the set of
values that are in the interval. We can easily perform many operations at the semantic level, including
equality, intersection, etc. This allows us to check that our implementation of intervals is
implementing the semantically correct behaviour.
-}

lowerBoundToValue :: Enum a => Interval.LowerBound a -> Maybe a
lowerBoundToValue (Interval.LowerBound (Interval.Finite b) inclusive) = Just $ if inclusive then b else succ b
lowerBoundToValue _                                                   = Nothing

upperBoundToValue :: Enum a => Interval.UpperBound a -> Maybe a
upperBoundToValue (Interval.UpperBound (Interval.Finite b) inclusive) = Just $ if inclusive then b else pred b
upperBoundToValue _                                                   = Nothing

intervalToSet :: (Ord a, Enum a) => Interval.Interval a -> Maybe (Set.Set a)
intervalToSet (Interval.Interval lb ub) = Set.fromList <$> (enumFromTo <$> lowerBoundToValue lb <*> upperBoundToValue ub)

setToInterval :: Set.Set a -> Interval.Interval a
setToInterval st | Set.null st = Interval.Interval (Interval.LowerBound Interval.PosInf True) (Interval.UpperBound Interval.NegInf True)
setToInterval st = Interval.Interval (Interval.LowerBound (Interval.Finite (Set.findMin st)) True) (Interval.UpperBound (Interval.Finite (Set.findMax st)) True)

prop_intervalSetTripping :: Property
prop_intervalSetTripping = property $ do
  ivl <- forAll genFiniteDiscreteInterval
  Hedgehog.tripping ivl (fromJust . intervalToSet) (Just . setToInterval)

prop_intervalSetEquals :: Property
prop_intervalSetEquals = property $ do
  ivl1 <- forAll genFiniteDiscreteInterval
  ivl2 <- forAll genFiniteDiscreteInterval
  s1 <- reoption $ intervalToSet ivl1
  s2 <- reoption $ intervalToSet ivl2
  Hedgehog.annotateShow s1
  Hedgehog.annotateShow s2
  let
    c1 = ivl1 == ivl2
    c2 = s2 == s1
  Hedgehog.cover 10 "True" $ c1
  Hedgehog.cover 10 "False" $ not c1
  c1 Hedgehog.=== c2

prop_intervalSetContains :: Property
prop_intervalSetContains = property $ do
  ivl1 <- forAll genFiniteDiscreteInterval
  ivl2 <- forAll genFiniteDiscreteInterval
  s1 <- reoption $ intervalToSet ivl1
  s2 <- reoption $ intervalToSet ivl2
  Hedgehog.annotateShow s1
  Hedgehog.annotateShow s2
  let
    c1 = ivl1 `Interval.contains` ivl2
    c2 = s2 `Set.isSubsetOf` s1
  Hedgehog.cover 30 "True" $ c1
  Hedgehog.cover 30 "False" $ not c1
  c1 Hedgehog.=== c2

prop_intervalSetIntersection :: Property
prop_intervalSetIntersection = property $ do
  ivl1 <- forAll genFiniteDiscreteInterval
  ivl2 <- forAll genFiniteDiscreteInterval
  let iv3 = ivl1 `Interval.intersection` ivl2
  s0 <- reoption $ intervalToSet iv3

  s1 <- reoption $ intervalToSet ivl1
  s2 <- reoption $ intervalToSet ivl2
  let s3 = s1 `Set.intersection` s2

  -- Just need some coverage of the interesting case
  Hedgehog.cover 5 "Non-trivial" $ not $ Set.null s3

  Hedgehog.annotateShow s0
  Hedgehog.annotateShow s1
  Hedgehog.annotateShow s2
  Hedgehog.annotateShow s3

  s0 Hedgehog.=== s3

tests :: TestTree
tests =
  testGroup
    "Interval"
    [ neverIsEmpty
    , alwaysIsNotEmpty
    , openIsEmpty
    , openOverlaps
    , eqLaws genDiscreteInterval
    , partialOrderLaws genDiscreteInterval Interval.contains
    , boundedLatticeLaws genDiscreteInterval
    , testGroup "properties"
      [ testProperty "intersection" intvlIntersection
      , testProperty "isEmpty" intvlIsEmpty
      , testProperty "overlaps" intvlOverlaps
      ]
    , testGroup "set model"
      [ testProperty "tripping" prop_intervalSetTripping
      , testProperty "equals" prop_intervalSetEquals
      , testProperty "contains" prop_intervalSetContains
      , testProperty "intersection" prop_intervalSetIntersection
      ]
    ]
