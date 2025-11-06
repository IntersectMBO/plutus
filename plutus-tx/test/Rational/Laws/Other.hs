-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

module Rational.Laws.Other (otherLaws) where

import Hedgehog (Gen, Property, assert, cover, property, (/==), (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusTx.Prelude qualified as Plutus
import PlutusTx.Ratio qualified as Ratio
import Prelude
import Rational.Laws.Helpers (forAllWithPP, genInteger, genIntegerPos, genRational,
                              testCoverProperty)
import Test.Tasty (TestTree)
import Test.Tasty.Hedgehog (testPropertyNamed)

otherLaws :: [TestTree]
otherLaws =
  [ testPropertyNamed
      "numerator r = numerator . scale (denominator r) $ r"
      "propNumeratorScale"
      propNumeratorScale
  , testPropertyNamed "denominator r >= 1" "propPosDen" propPosDen
  , testPropertyNamed "recip r * r = 1 for r /= 0" "propRecipSelf" propRecipSelf
  , testPropertyNamed "abs r >= 0" "propAbs" propAbs
  , testPropertyNamed "abs r * abs r' = abs (r * r')" "probAbsTimes" propAbsTimes
  , testPropertyNamed "r = n + f, where (n, f) = properFraction r" "propProperFrac" propProperFrac
  , testCoverProperty "signs of properFraction components match sign of input" propProperFracSigns
  , testPropertyNamed "abs f < 1, where (_, f) = properFraction r" "propProperFracAbs" propProperFracAbs
  , testPropertyNamed
      "abs (round r) >= abs n, where (n, _) = properFraction r"
      "propAbsRound"
      propAbsRound
  , testPropertyNamed "halves round as expected" "propRoundHalf" propRoundHalf
  , testPropertyNamed
      ( "if abs f < half, then round r = truncate r, "
          <> "where (_, f) = properFraction r"
      )
      "propRoundLow"
      propRoundLow
  , testPropertyNamed
      ( "if abs f > half, then abs (round r) = abs (truncate r) + 1, "
          <> "where (_, f) = properFraction r"
      )
      "propRoundHigh"
      propRoundHigh
  ]

-- Helpers

propNumeratorScale :: Property
propNumeratorScale = property $ do
  r <- forAllWithPP genRational
  Ratio.numerator r === (Ratio.numerator . Plutus.scale (Ratio.denominator r) $ r)

propPosDen :: Property
propPosDen = property $ do
  r <- forAllWithPP genRational
  assert (Ratio.denominator r Plutus.>= Plutus.one)

propRecipSelf :: Property
propRecipSelf = property $ do
  r <- forAllWithPP . Gen.filter (/= Plutus.zero) $ genRational
  Ratio.recip r Plutus.* r === Plutus.one

propAbs :: Property
propAbs = property $ do
  r <- forAllWithPP genRational
  assert (Ratio.abs r >= Plutus.zero)

propAbsTimes :: Property
propAbsTimes = property $ do
  r <- forAllWithPP genRational
  r' <- forAllWithPP genRational
  Ratio.abs r Plutus.* Ratio.abs r' === Ratio.abs (r Plutus.* r')

propProperFrac :: Property
propProperFrac = property $ do
  r <- forAllWithPP genRational
  let (n, f) = Ratio.properFraction r
  r === Ratio.fromInteger n Plutus.+ f

propProperFracSigns :: Property
propProperFracSigns = property $ do
  r <- forAllWithPP go
  cover 30 "zero" $ r Plutus.== Plutus.zero
  cover 30 "negative" $ r Plutus.< Plutus.zero
  cover 30 "positive" $ r Plutus.> Plutus.zero
  let (n, f) = Ratio.properFraction r
  case Plutus.compare r Plutus.zero of
    Plutus.EQ -> do
      Plutus.compare n Plutus.zero === Plutus.EQ
      Plutus.compare f Plutus.zero === Plutus.EQ
    Plutus.GT -> do
      Plutus.compare n Plutus.zero /== Plutus.LT
      Plutus.compare f Plutus.zero /== Plutus.LT
    Plutus.LT -> do
      Plutus.compare n Plutus.zero /== Plutus.GT
      Plutus.compare n Plutus.zero /== Plutus.GT
 where
  go :: Gen Plutus.Rational
  go = Gen.choice [zeroNum, sameSign, diffSign]
  zeroNum :: Gen Plutus.Rational
  zeroNum = Ratio.unsafeRatio Plutus.zero <$> Gen.filter (/= Plutus.zero) genInteger
  sameSign :: Gen Plutus.Rational
  sameSign = do
    gen <- Gen.element [genIntegerPos, negate <$> genIntegerPos]
    Ratio.unsafeRatio <$> gen <*> gen
  diffSign :: Gen Plutus.Rational
  diffSign = do
    (genN, genD) <-
      Gen.element
        [ (genIntegerPos, negate <$> genIntegerPos)
        , (negate <$> genIntegerPos, genIntegerPos)
        ]
    Ratio.unsafeRatio <$> genN <*> genD

propProperFracAbs :: Property
propProperFracAbs = property $ do
  r <- forAllWithPP genRational
  let (_, f) = Ratio.properFraction r
  assert (Ratio.abs f Plutus.< Plutus.one)

propAbsRound :: Property
propAbsRound = property $ do
  r <- forAllWithPP genRational
  let rounded = Ratio.round r
  let (n, _) = Ratio.properFraction r
  assert (Plutus.abs rounded Plutus.>= Plutus.abs n)

propRoundHalf :: Property
propRoundHalf = property $ do
  (n, f) <- forAllWithPP go
  let r = Ratio.fromInteger n Plutus.+ f
  let rounded = Ratio.round r
  case (signum n, even n) of
    (-1, False) -> rounded === n Plutus.- Plutus.one
    (-1, True)  -> rounded === n
    (0, _)      -> rounded === Plutus.zero
    (1, False)  -> rounded === n Plutus.+ Plutus.one
    _           -> rounded === n
 where
  half = Ratio.unsafeRatio 1 2

  go :: Gen (Integer, Plutus.Rational)
  go = do
    n <- genInteger
    f <- case signum n of
      (-1) -> pure . Ratio.negate $ half
      0    -> Gen.element [half, Ratio.negate half]
      _    -> pure half
    pure (n, f)

propRoundLow :: Property
propRoundLow = property $ do
  (n, f) <- forAllWithPP go
  let r = Ratio.fromInteger n Plutus.+ f
  let rounded = Ratio.round r
  let truncated = Ratio.truncate r
  rounded === truncated
 where
  go :: Gen (Integer, Plutus.Rational)
  go = do
    num <- Gen.integral . Range.constant 1 $ 135
    let f = Ratio.unsafeRatio num 271
    n <- genInteger
    case signum n of
      (-1) -> pure (n, Ratio.negate f)
      0    -> (n,) <$> Gen.element [f, Ratio.negate f]
      _    -> pure (n, f)

propRoundHigh :: Property
propRoundHigh = property $ do
  (n, f) <- forAllWithPP go
  let r = Ratio.fromInteger n Plutus.+ f
  let rounded = Ratio.round r
  let truncated = Ratio.truncate r
  Plutus.abs rounded === Plutus.abs truncated Plutus.+ Plutus.one
 where
  go :: Gen (Integer, Plutus.Rational)
  go = do
    num <- Gen.integral . Range.constant 136 $ 270
    let f = Ratio.unsafeRatio num 271
    n <- genInteger
    case signum n of
      (-1) -> pure (n, Ratio.negate f)
      0    -> (n,) <$> Gen.element [f, Ratio.negate f]
      _    -> pure (n, f)
