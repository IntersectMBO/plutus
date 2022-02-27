module Suites.Laws.Multiplicative (multiplicativeLaws) where

import Hedgehog (Property, property)
import PlutusTx.Prelude qualified as Plutus
import Prelude
import Suites.Laws.Helpers (forAllWithPP, genRational, normalAndEquivalentTo)
import Test.Tasty (TestTree)
import Test.Tasty.Hedgehog (testProperty)

multiplicativeLaws :: [TestTree]
multiplicativeLaws = [
  testProperty "* associates" propTimesAssoc,
  testProperty "one is a left identity" propOneLeftId,
  testProperty "one is a right identity" propOneRightId
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
