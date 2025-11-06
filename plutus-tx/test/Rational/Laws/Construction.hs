-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Rational.Laws.Construction (constructionLaws) where

import Data.Ratio qualified as GHC
import Hedgehog (Gen, Property, assert, cover, property, (===))
import Hedgehog.Gen qualified as Gen
import PlutusTx.Enum qualified as P
import PlutusTx.List qualified as P
import PlutusTx.Numeric qualified as P
import PlutusTx.Prelude qualified as Plutus
import PlutusTx.Ratio qualified as P
import Rational.Laws.Helpers (
  forAllWithPP,
  genInteger,
  genIntegerPos,
  genRational,
  normalAndEquivalentToMaybe,
  testCoverProperty,
 )
import Test.Tasty (TestTree)
import Test.Tasty.Hedgehog (testPropertyNamed)
import Prelude hiding (pred, succ)

constructionLaws :: [TestTree]
constructionLaws =
  [ testPropertyNamed "ratio x 0 = Nothing" "propZeroDenom" propZeroDenom
  , testPropertyNamed "ratio x 1 = Just . fromInteger $ x" "propOneDenom" propOneDenom
  , testPropertyNamed "ratio x x = Just 1 for x /= 0" "propRatioSelf" propRatioSelf
  , testCoverProperty "sign of result depends on signs of arguments" propRatioSign
  , testPropertyNamed
      "if ratio x y = Just r, then unsafeRatio x y = r"
      "propConstructionAgreement"
      propConstructionAgreement
  , testPropertyNamed
      "if r = fromInteger x, then numerator r = x"
      "propFromIntegerNum"
      propFromIntegerNum
  , testPropertyNamed
      "if r = fromInteger x, then denominator r = 1"
      "propFromIntegerDen"
      propFromIntegerDen
  , testPropertyNamed "ratio x y = ratio (x * z) (y * z) for z /= 0" "propRatioScale" propRatioScale
  , testPropertyNamed
      "denominator (unsafeRatio x y) > 0"
      "propUnsafeRatioDenomPos"
      propUnsafeRatioDenomPos
  , testPropertyNamed
      "succ(r)>r"
      "propSuccGt"
      propSuccGt
  , testPropertyNamed
      "pred(r)<r"
      "propPredLt"
      propPredLt
  , testPropertyNamed
      "fromEnum . toEnum n = n"
      "propFromToEnumId"
      propFromToEnumId
  , testPropertyNamed
      "denominator . toEnum = 1"
      "propDenomToEnum"
      propDenomToEnum
  , testPropertyNamed
      "n<=m ==> length(enumFromTo n m) = abs(n-m)+1"
      "propEnumFromToInteger"
      propEnumFromToInteger
  , testPropertyNamed
      "enumFromTo = GHC.enumFromTo"
      "propEnumFromToGHC"
      propEnumFromToGHC
  , testPropertyNamed
      "x/=y ==> enumFromThenTo x y x = [x]"
      "propEnumFromThenToLim"
      propEnumFromThenToLim
  , testPropertyNamed
      "x/=y ==> enumFromThenTo = GHC.enumFromThenTo"
      "propEnumFromThenToGHC"
      propEnumFromThenToGHC
  , testPropertyNamed
      "enumFromTo x y = enumFromThenTo x (x+1) y"
      "propEnumFromToThenTo"
      propEnumFromToThenTo
  ]

propZeroDenom :: Property
propZeroDenom = property $ do
  x <- forAllWithPP genInteger
  P.ratio x Plutus.zero `normalAndEquivalentToMaybe` Nothing

propOneDenom :: Property
propOneDenom = property $ do
  x <- forAllWithPP genInteger
  P.ratio x Plutus.one `normalAndEquivalentToMaybe` (Just . P.fromInteger $ x)

propRatioSelf :: Property
propRatioSelf = property $ do
  x <- forAllWithPP . Gen.filter (/= Plutus.zero) $ genInteger
  P.ratio x x `normalAndEquivalentToMaybe` Just Plutus.one

propRatioSign :: Property
propRatioSign = property $ do
  (n, d) <- forAllWithPP go
  cover 30 "zero numerator" $ n == 0
  cover 30 "same signs" $ signum n == signum d
  cover 30 "different signs" $ (signum n /= signum d) && n /= 0
  let r = P.ratio n d
  let signIndicator = Plutus.compare <$> r <*> pure Plutus.zero
  case (signum n, signum d) of
    (0, _) -> signIndicator === Just Plutus.EQ
    (-1, -1) -> signIndicator === Just Plutus.GT
    (1, 1) -> signIndicator === Just Plutus.GT
    _ -> signIndicator === Just Plutus.LT
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
    (genN, genD) <-
      Gen.element
        [ (genIntegerPos, negate <$> genIntegerPos)
        , (negate <$> genIntegerPos, genIntegerPos)
        ]
    (,) <$> genN <*> genD

propConstructionAgreement :: Property
propConstructionAgreement = property $ do
  n <- forAllWithPP genInteger
  d <- forAllWithPP . Gen.filter (/= Plutus.zero) $ genInteger
  P.ratio n d `normalAndEquivalentToMaybe` (Just . P.unsafeRatio n $ d)

propFromIntegerNum :: Property
propFromIntegerNum = property $ do
  x <- forAllWithPP genInteger
  let r = P.fromInteger x
  P.numerator r === x

propFromIntegerDen :: Property
propFromIntegerDen = property $ do
  x <- forAllWithPP genInteger
  let r = P.fromInteger x
  P.denominator r === Plutus.one

propRatioScale :: Property
propRatioScale = property $ do
  x <- forAllWithPP genInteger
  y <- forAllWithPP genInteger
  z <- forAllWithPP . Gen.filter (/= Plutus.zero) $ genInteger
  let lhs = P.ratio x y
  let rhs = P.ratio (x Plutus.* z) (y Plutus.* z)
  lhs `normalAndEquivalentToMaybe` rhs

propUnsafeRatioDenomPos :: Property
propUnsafeRatioDenomPos = property $ do
  n <- forAllWithPP genInteger
  d <- forAllWithPP $ Gen.filter (/= Plutus.zero) genInteger
  assert $ P.denominator (P.unsafeRatio n d) > 0

propSuccGt :: Property
propSuccGt = property $ do
  n <- forAllWithPP genRational
  assert $ P.succ n > n

propPredLt :: Property
propPredLt = property $ do
  n <- forAllWithPP genRational
  assert $ P.pred n < n

propDenomToEnum :: Property
propDenomToEnum = property $ do
  n <- forAllWithPP genInteger
  P.denominator (P.toEnum n) === 1

propFromToEnumId :: Property
propFromToEnumId = property $ do
  n <- forAllWithPP genInteger
  P.fromEnum @P.Rational (P.toEnum n) === n

propEnumFromToInteger :: Property
propEnumFromToInteger = property $ do
  n <- forAllWithPP genInteger
  m <- forAllWithPP $ Gen.filter (>= n) genInteger
  P.length (P.enumFromTo @P.Rational (P.toEnum n) (P.toEnum m)) === abs (n - m) + 1

propEnumFromThenToLim :: Property
propEnumFromThenToLim = property $ do
  x <- forAllWithPP genRational
  y <- forAllWithPP $ Gen.filter (/= x) genRational
  P.enumFromThenTo x y x === [x]

propEnumFromToGHC :: Property
propEnumFromToGHC = property $ do
  x <- forAllWithPP genRational
  y <- forAllWithPP genRational
  fmap toGHC (P.enumFromTo x y) === enumFromTo (toGHC x) (toGHC y)

propEnumFromThenToGHC :: Property
propEnumFromThenToGHC = property $ do
  x <- forAllWithPP genRational
  y <- forAllWithPP $ Gen.filter (/= x) genRational
  z <- forAllWithPP genRational
  fmap toGHC (P.enumFromThenTo x y z) === enumFromThenTo (toGHC x) (toGHC y) (toGHC z)

propEnumFromToThenTo :: Property
propEnumFromToThenTo = property $ do
  x <- forAllWithPP genRational
  y <- forAllWithPP genRational
  P.enumFromTo x y === P.enumFromThenTo x (x P.+ Plutus.one) y

{-| Converts a 'Rational' to a GHC 'Rational', preserving value. Does not
work on-chain.
-}
toGHC :: P.Rational -> Rational
toGHC r = P.numerator r GHC.% P.denominator r
