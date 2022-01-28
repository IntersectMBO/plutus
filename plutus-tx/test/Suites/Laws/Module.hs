module Suites.Laws.Module (moduleLaws) where

import Hedgehog (Property, property)
import PlutusTx.Prelude qualified as Plutus
import Prelude
import Suites.Laws.Helpers (forAllWithPP, genInteger, genRational, normalAndEquivalentTo)
import Test.Tasty (TestTree)
import Test.Tasty.Hedgehog (testProperty)

moduleLaws :: [TestTree]
moduleLaws = [
  testProperty "scale 0 = 0" propScaleZero,
  testProperty "scale 1 = id" propScaleOne,
  testProperty "scale distributes over +" propScaleDistPlus,
  testProperty "scale x (scale y r) = scale (x * y) r" propScaleTimes
  ]

propScaleZero :: Property
propScaleZero = property $ do
  x <- forAllWithPP genRational
  Plutus.scale Plutus.zero x `normalAndEquivalentTo` Plutus.zero

propScaleOne :: Property
propScaleOne = property $ do
  x <- forAllWithPP genRational
  Plutus.scale Plutus.one x `normalAndEquivalentTo` x

propScaleDistPlus :: Property
propScaleDistPlus = property $ do
  x <- forAllWithPP genInteger
  y <- forAllWithPP genRational
  z <- forAllWithPP genRational
  let lhs = Plutus.scale x (y Plutus.+ z)
  let rhs = Plutus.scale x y Plutus.+ Plutus.scale x z
  lhs `normalAndEquivalentTo` rhs

propScaleTimes :: Property
propScaleTimes = property $ do
  x <- forAllWithPP genInteger
  y <- forAllWithPP genInteger
  r <- forAllWithPP genRational
  let lhs = Plutus.scale x (Plutus.scale y r)
  let rhs = Plutus.scale (x Plutus.* y) r
  lhs `normalAndEquivalentTo` rhs
