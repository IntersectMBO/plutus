{-# LANGUAGE OverloadedStrings #-}

module Hedgehog.Laws.Lattice where

import Hedgehog (Property, cover, forAll, property)
import Hedgehog qualified
import Hedgehog.Laws.Common
import PlutusTx.Lattice
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import Prelude

joinLatticeLaws :: (Show a, Eq a, JoinSemiLattice a) => Hedgehog.Gen a -> TestTree
joinLatticeLaws g =
  testGroup
    "join semilattice laws"
    [ testProperty "idempotent" (prop_idempotent g (\/))
    , testProperty "commutative" (prop_commutative g (\/))
    , testProperty "associative" (prop_associative g (\/))
    ]

boundedJoinLatticeLaws :: (Show a, Eq a, BoundedJoinSemiLattice a) => Hedgehog.Gen a -> TestTree
boundedJoinLatticeLaws g =
  testGroup
    "bounded join semilattice laws"
    [ joinLatticeLaws g
    , testProperty "unit" (prop_unit g (\/) bottom)
    ]

meetLatticeLaws :: (Show a, Eq a, MeetSemiLattice a) => Hedgehog.Gen a -> TestTree
meetLatticeLaws g =
  testGroup
    "meet semilattice laws"
    [ testProperty "idempotent" (prop_idempotent g (/\))
    , testProperty "commutative" (prop_commutative g (/\))
    , testProperty "associative" (prop_associative g (/\))
    ]

boundedMeetLatticeLaws :: (Show a, Eq a, BoundedMeetSemiLattice a) => Hedgehog.Gen a -> TestTree
boundedMeetLatticeLaws g =
  testGroup
    "bounded meet semilattice laws"
    [ meetLatticeLaws g
    , testProperty "unit" (prop_unit g (/\) top)
    ]

prop_latticeAbsorb :: (Show a, Eq a, Lattice a) => Hedgehog.Gen a -> Property
prop_latticeAbsorb g = property $ do
  x <- forAll g
  y <- forAll g
  cover 10 "different" $ x /= y
  x \/ (x /\ y) Hedgehog.=== x
  x /\ (x \/ y) Hedgehog.=== x

latticeLaws :: (Show a, Eq a, Lattice a) => Hedgehog.Gen a -> TestTree
latticeLaws g =
  testGroup
    "lattice laws"
    [ joinLatticeLaws g
    , meetLatticeLaws g
    , testProperty "absorption" (prop_latticeAbsorb g)
    ]

boundedLatticeLaws :: (Show a, Eq a, BoundedLattice a) => Hedgehog.Gen a -> TestTree
boundedLatticeLaws g =
  testGroup
    "bounded lattice laws"
    [ boundedJoinLatticeLaws g
    , boundedMeetLatticeLaws g
    , testProperty "absorption" (prop_latticeAbsorb g)
    ]
