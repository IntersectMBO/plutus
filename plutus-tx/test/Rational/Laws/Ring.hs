-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}

module Rational.Laws.Ring (ringLaws) where

import Hedgehog (Property, property, (===))
import PlutusTx.Prelude qualified as Plutus
import Rational.Laws.Helpers (forAllWithPP, genRational)
import Test.Tasty (TestTree)
import Test.Tasty.Hedgehog (testPropertyNamed)
import Prelude

ringLaws :: [TestTree]
ringLaws =
  [ testPropertyNamed "zero is a left annihilator" "propZeroLeftAnnih" propZeroLeftAnnih
  , testPropertyNamed "zero is a right annihilator" "propZeroRightAnnih" propZeroRightAnnih
  , testPropertyNamed "* left-distributes over +" "propTimesLeftDistPlus" propTimesLeftDistPlus
  , testPropertyNamed "* right-distributes over +" "propTimesRightDistPlus" propTimesRightDistPlus
  ]

-- Helpers

propZeroLeftAnnih :: Property
propZeroLeftAnnih = property $ do
  x <- forAllWithPP genRational
  Plutus.zero Plutus.* x === Plutus.zero

propZeroRightAnnih :: Property
propZeroRightAnnih = property $ do
  x <- forAllWithPP genRational
  x Plutus.* Plutus.zero === Plutus.zero

propTimesLeftDistPlus :: Property
propTimesLeftDistPlus = property $ do
  x <- forAllWithPP genRational
  y <- forAllWithPP genRational
  z <- forAllWithPP genRational
  x Plutus.* (y Plutus.+ z) === (x Plutus.* y) Plutus.+ (x Plutus.* z)

propTimesRightDistPlus :: Property
propTimesRightDistPlus = property $ do
  x <- forAllWithPP genRational
  y <- forAllWithPP genRational
  z <- forAllWithPP genRational
  (x Plutus.+ y) Plutus.* z === (x Plutus.* z) Plutus.+ (y Plutus.* z)
