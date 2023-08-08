-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

module Rational.Laws.Construction (constructionLaws) where

import Hedgehog (Gen, Property, cover, property, (===))
import Hedgehog.Gen qualified as Gen
import PlutusTx.Prelude qualified as Plutus
import PlutusTx.Ratio qualified as Ratio
import Prelude
import Rational.Laws.Helpers (forAllWithPP, genInteger, genIntegerPos, normalAndEquivalentToMaybe,
                              testCoverProperty)
import Test.Tasty (TestTree)
import Test.Tasty.Hedgehog (testPropertyNamed)

constructionLaws :: [TestTree]
constructionLaws = [
  testPropertyNamed "ratio x 0 = Nothing" "propZeroDenom" propZeroDenom,
  testPropertyNamed "ratio x 1 = Just . fromInteger $ x" "propOneDenom" propOneDenom,
  testPropertyNamed "ratio x x = Just 1 for x /= 0" "propRatioSelf" propRatioSelf,
  testCoverProperty "sign of result depends on signs of arguments" propRatioSign,
  testPropertyNamed "if ratio x y = Just r, then unsafeRatio x y = r" "propConstructionAgreement" propConstructionAgreement,
  testPropertyNamed "if r = fromInteger x, then numerator r = x" "propFromIntegerNum" propFromIntegerNum,
  testPropertyNamed "if r = fromInteger x, then denominator r = 1" "propFromIntegerDen" propFromIntegerDen,
  testPropertyNamed "ratio x y = ratio (x * z) (y * z) for z /= 0" "propRatioScale" propRatioScale
  ]

-- Helpers

propZeroDenom :: Property
propZeroDenom = property $ do
  x <- forAllWithPP genInteger
  Ratio.ratio x Plutus.zero `normalAndEquivalentToMaybe` Nothing

propOneDenom :: Property
propOneDenom = property $ do
  x <- forAllWithPP genInteger
  Ratio.ratio x Plutus.one `normalAndEquivalentToMaybe` (Just . Ratio.fromInteger $ x)

propRatioSelf :: Property
propRatioSelf = property $ do
  x <- forAllWithPP . Gen.filter (/= Plutus.zero) $ genInteger
  Ratio.ratio x x `normalAndEquivalentToMaybe` Just Plutus.one

propRatioSign :: Property
propRatioSign = property $ do
  (n, d) <- forAllWithPP go
  cover 30 "zero numerator" $ n == 0
  cover 30 "same signs" $ signum n == signum d
  cover 30 "different signs" $ (signum n /= signum d) && n /= 0
  let r = Ratio.ratio n d
  let signIndicator = Plutus.compare <$> r <*> pure Plutus.zero
  case (signum n, signum d) of
    (0, _)   -> signIndicator === Just Plutus.EQ
    (-1, -1) -> signIndicator === Just Plutus.GT
    (1, 1)   -> signIndicator === Just Plutus.GT
    _        -> signIndicator === Just Plutus.LT
  where
    go :: Gen (Plutus.Integer, Plutus.Integer)
    go = Gen.choice [zeroNum, sameSign, diffSign]
    zeroNum :: Gen (Plutus.Integer, Plutus.Integer)
    zeroNum = (0,) <$> Gen.filter (/= Plutus.zero) genInteger
    sameSign :: Gen (Plutus.Integer, Plutus.Integer)
    sameSign = do
      gen <- Gen.element [genIntegerPos, negate <$> genIntegerPos]
      (,) <$> gen <*> gen
    diffSign :: Gen (Plutus.Integer, Plutus.Integer)
    diffSign = do
      (genN, genD) <- Gen.element [(genIntegerPos, negate <$> genIntegerPos),
                                   (negate <$> genIntegerPos, genIntegerPos)]
      (,) <$> genN <*> genD

propConstructionAgreement :: Property
propConstructionAgreement = property $ do
  n <- forAllWithPP genInteger
  d <- forAllWithPP . Gen.filter (/= Plutus.zero) $ genInteger
  Ratio.ratio n d `normalAndEquivalentToMaybe` (Just . Ratio.unsafeRatio n $ d)

propFromIntegerNum :: Property
propFromIntegerNum = property $ do
  x <- forAllWithPP genInteger
  let r = Ratio.fromInteger x
  Ratio.numerator r === x

propFromIntegerDen :: Property
propFromIntegerDen = property $ do
  x <- forAllWithPP genInteger
  let r = Ratio.fromInteger x
  Ratio.denominator r === Plutus.one

propRatioScale :: Property
propRatioScale = property $ do
  x <- forAllWithPP genInteger
  y <- forAllWithPP genInteger
  z <- forAllWithPP . Gen.filter (/= Plutus.zero) $ genInteger
  let lhs = Ratio.ratio x y
  let rhs = Ratio.ratio (x Plutus.* z) (y Plutus.* z)
  lhs `normalAndEquivalentToMaybe` rhs
