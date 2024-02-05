{-# LANGUAGE OverloadedStrings #-}

module Rational.Laws.Additive (additiveLaws) where

import Hedgehog (Property, property)
import PlutusTx.Prelude qualified as Plutus
import Rational.Laws.Helpers (forAllWithPP, genRational, normalAndEquivalentTo)
import Test.Tasty (TestTree)
import Test.Tasty.Hedgehog (testPropertyNamed)
import Prelude

additiveLaws :: [TestTree]
additiveLaws =
  [ testPropertyNamed "+ commutes" "propPlusComm" propPlusComm
  , testPropertyNamed "+ associates" "propPlusAssoc" propPlusAssoc
  , testPropertyNamed "zero is an identity" "propZeroId" propZeroId
  , testPropertyNamed "x - x = zero" "propMinusCancel" propMinusCancel
  , testPropertyNamed "negate . negate = id" "propDoubleNeg" propDoubleNeg
  ]

-- Helpers

propPlusComm :: Property
propPlusComm = property $ do
  x <- forAllWithPP genRational
  y <- forAllWithPP genRational
  (x Plutus.+ y) `normalAndEquivalentTo` (y Plutus.+ x)

propPlusAssoc :: Property
propPlusAssoc = property $ do
  x <- forAllWithPP genRational
  y <- forAllWithPP genRational
  z <- forAllWithPP genRational
  ((x Plutus.+ y) Plutus.+ z) `normalAndEquivalentTo` (x Plutus.+ (y Plutus.+ z))

propZeroId :: Property
propZeroId = property $ do
  x <- forAllWithPP genRational
  (x Plutus.+ Plutus.zero) `normalAndEquivalentTo` x

propMinusCancel :: Property
propMinusCancel = property $ do
  x <- forAllWithPP genRational
  (x Plutus.- x) `normalAndEquivalentTo` Plutus.zero

propDoubleNeg :: Property
propDoubleNeg = property $ do
  x <- forAllWithPP genRational
  (Plutus.negate . Plutus.negate $ x) `normalAndEquivalentTo` x
