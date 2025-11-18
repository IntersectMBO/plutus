{-# LANGUAGE OverloadedStrings #-}

module Rational.Laws.Multiplicative (multiplicativeLaws) where

import Hedgehog (Property, property)
import PlutusTx.Prelude qualified as Plutus
import Rational.Laws.Helpers (forAllWithPP, genRational, normalAndEquivalentTo)
import Test.Tasty (TestTree)
import Test.Tasty.Hedgehog (testPropertyNamed)
import Prelude

multiplicativeLaws :: [TestTree]
multiplicativeLaws =
  [ testPropertyNamed "* associates" "propTimesAssoc" propTimesAssoc
  , testPropertyNamed "one is a left identity" "propOneLeftId" propOneLeftId
  , testPropertyNamed "one is a right identity" "propOneRightId" propOneRightId
  ]

-- Helpers

propTimesAssoc :: Property
propTimesAssoc = property $ do
  x <- forAllWithPP genRational
  y <- forAllWithPP genRational
  z <- forAllWithPP genRational
  let lhs = (x Plutus.* y) Plutus.* z
  let rhs = x Plutus.* (y Plutus.* z)
  lhs `normalAndEquivalentTo` rhs

propOneLeftId :: Property
propOneLeftId = property $ do
  x <- forAllWithPP genRational
  (Plutus.one Plutus.* x) `normalAndEquivalentTo` x

propOneRightId :: Property
propOneRightId = property $ do
  x <- forAllWithPP genRational
  (x Plutus.* Plutus.one) `normalAndEquivalentTo` x
