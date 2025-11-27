{-# LANGUAGE OverloadedStrings #-}

module Hedgehog.Laws.Common where

import Hedgehog (Property, cover, forAll, property)
import Hedgehog qualified
import Prelude

implies :: Bool -> Bool -> Bool
implies x y = not x || y

prop_idempotent :: (Show a, Eq a) => Hedgehog.Gen a -> (a -> a -> a) -> Property
prop_idempotent g op = property $ do
  x <- forAll g
  x `op` x Hedgehog.=== x

prop_commutative :: (Show a, Eq a) => Hedgehog.Gen a -> (a -> a -> a) -> Property
prop_commutative g op = property $ do
  x <- forAll g
  y <- forAll g
  cover 10 "different" $ x /= y
  cover 5 "same" $ x == y
  x `op` y Hedgehog.=== y `op` x

prop_associative :: (Show a, Eq a) => Hedgehog.Gen a -> (a -> a -> a) -> Property
prop_associative g op = property $ do
  x <- forAll g
  y <- forAll g
  z <- forAll g
  cover 10 "different" $ x /= y && y /= z
  cover 5 "same" $ x == y || y == z || z == x
  (x `op` y) `op` z Hedgehog.=== x `op` (y `op` z)

prop_unit :: (Show a, Eq a) => Hedgehog.Gen a -> (a -> a -> a) -> a -> Property
prop_unit g op unit = property $ do
  x <- forAll g
  cover 10 "different" $ x /= unit
  x `op` unit Hedgehog.=== x

prop_reflexive :: Show a => Hedgehog.Gen a -> (a -> a -> Bool) -> Property
prop_reflexive g op = property $ do
  x <- forAll g
  x `op` x Hedgehog.=== True

prop_symmetric :: (Show a, Eq a) => Hedgehog.Gen a -> (a -> a -> Bool) -> Property
prop_symmetric g op = property $ do
  x <- forAll g
  y <- forAll g
  cover 10 "different" $ x /= y
  cover 5 "same" $ x == y
  x `op` y Hedgehog.=== y `op` x

prop_transitive :: (Show a, Eq a) => Hedgehog.Gen a -> (a -> a -> Bool) -> Property
prop_transitive g op = property $ do
  x <- forAll g
  y <- forAll g
  z <- forAll g
  cover 10 "different" $ x /= y && y /= z
  cover 5 "same" $ x == y || y == z || z == x
  Hedgehog.assert $ (x `op` y && y `op` z) `implies` (x `op` z)

prop_antisymmetric :: (Show a, Eq a) => Hedgehog.Gen a -> (a -> a -> Bool) -> Property
prop_antisymmetric g op = property $ do
  x <- forAll g
  y <- forAll g
  cover 10 "different" $ x /= y
  cover 5 "same" $ x == y
  Hedgehog.assert $ (x `op` y && y `op` x) `implies` (x == y)

prop_total :: (Show a, Eq a) => Hedgehog.Gen a -> (a -> a -> Bool) -> Property
prop_total g op = property $ do
  x <- forAll g
  y <- forAll g
  cover 10 "different" $ x /= y
  cover 5 "same" $ x == y
  Hedgehog.assert $ x `op` y || y `op` x
