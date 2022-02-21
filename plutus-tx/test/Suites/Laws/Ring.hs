module Suites.Laws.Ring (ringLaws) where

import Hedgehog (Property, property, (===))
import PlutusTx.Prelude qualified as Plutus
import Prelude
import Suites.Laws.Helpers (forAllWithPP, genRational)
import Test.Tasty (TestTree)
import Test.Tasty.Hedgehog (testProperty)

ringLaws :: [TestTree]
ringLaws = [
  testProperty "zero is a left annihilator" propZeroLeftAnnih,
  testProperty "zero is a right annihilator" propZeroRightAnnih,
  testProperty "* left-distributes over +" propTimesLeftDistPlus,
  testProperty "* right-distributes over +" propTimesRightDistPlus
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


