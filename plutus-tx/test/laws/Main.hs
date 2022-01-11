{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TupleSections      #-}
{-# OPTIONS_GHC -Wno-orphans #-} -- We need an Arg instance for hedgehog-fn

module Main (main) where

import Prelude

import Data.Aeson (decode, encode)
import Data.Functor.Contravariant (contramap)
import Data.Kind (Type)
import Hedgehog (Gen, Property, assert, cover, forAllWith, property, success, tripping, (/==), (===))
import Hedgehog.Function (Arg (build), CoGen, fnWith, forAllFn, vary, via)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusTx.IsData.Class (fromBuiltinData, toBuiltinData, unsafeFromBuiltinData)
import PlutusTx.Prelude qualified as Plutus
import PlutusTx.Ratio qualified as Ratio
import Test.Tasty (defaultMain, localOption, testGroup)
import Test.Tasty.Hedgehog (HedgehogTestLimit (HedgehogTestLimit), testProperty)
import Text.Show.Pretty (ppShow)

main :: IO ()
main = defaultMain . localOption (HedgehogTestLimit . Just $ 1000) . testGroup "Rational" $ [
  testGroup "Eq" [
    testProperty "== is reflexive" propEqRefl,
    testProperty "== is symmetric" propEqSymm,
    testProperty "== is transitive" propEqTrans,
    testProperty "== implies substitution" propEqSub
    ],
  testGroup "Ord" [
    testProperty "<= is reflexive" propOrdRefl,
    testProperty "<= is anti-symmetric" propOrdAntiSymm,
    testProperty "<= is transitive" propOrdTrans,
    testProperty "== implies EQ" propOrdCompare
    ],
  testGroup "AdditiveGroup" [
    testProperty "+ commutes" propPlusComm,
    testProperty "+ associates" propPlusAssoc,
    testProperty "zero is an identity" propZeroId,
    testProperty "x - x = zero" propMinusCancel,
    testProperty "negate . negate = id" propDoubleNeg
    ],
  testGroup "MultiplicativeMonoid" [
    testProperty "* associates" propTimesAssoc,
    testProperty "one is a left identity" propOneLeftId,
    testProperty "one is a right identity" propOneRightId
    ],
  testGroup "Ring" [
    testProperty "zero is a left annihilator" propZeroLeftAnnih,
    testProperty "zero is a right annihilator" propZeroRightAnnih,
    testProperty "* left-distributes over +" propTimesLeftDistPlus,
    testProperty "* right-distributes over +" propTimesRightDistPlus
    ],
  testGroup "Module" [
    testProperty "scale one = id" propScaleOne,
    testProperty "scale distributes over +" propScaleDistPlus,
    testProperty "scale x (scale y r) = scale (x * y) r" propScaleTimes
    ],
  testGroup "Serialization" [
    testProperty "FromBuiltinData-ToBuiltinData roundtrip" propIsDataRound,
    testProperty "unsafeFromBuiltinData . toBuiltinData = id" propUnsafeIsData,
    testProperty "FromJSON-ToJSON roundtrip" propIsJSONRound
    ],
  testGroup "Construction" [
    testProperty "ratio x 0 = Nothing" propZeroDenom,
    testProperty "ratio x 1 = Just . fromInteger $ x" propOneDenom,
    testProperty "ratio x x = Just 1 for x /= 0" propRatioSelf,
    testProperty "sign of result depends on signs of arguments" propRatioSign,
    testProperty "if ratio x y = Just r, then unsafeRatio x y = r" propConstructionAgreement,
    testProperty "if r = fromInteger x, then numerator r = x" propFromIntegerNum,
    testProperty "if r = fromInteger x, then denominator r = 1" propFromIntegerDen,
    testProperty "ratio x y = ratio (x * z) (y * z) for z /= 0" propRatioScale
    ],
  testGroup "Other" [
    testProperty "numerator r = numerator . scale (denominator r) $ r" propNumeratorScale,
    testProperty "denominator r >= 1" propPosDen,
    testProperty "recip r * r = 1 for r /= 0" propRecipSelf,
    testProperty "abs r >= 0" propAbs,
    testProperty "abs r * abs r' = abs (r * r')" propAbsTimes,
    testProperty "r = n + f, where (n, f) = properFraction r" propProperFrac,
    testProperty "signs of properFraction components match signs of input" propProperFracSigns,
    testProperty "abs f < 1, where (_, f) = properFraction r" propProperFracAbs,
    testProperty "abs (round r) >= abs n, where (n, _) = properFraction r" propAbsRound,
    testProperty "halves round as expected" propRoundHalf,
    testProperty ("if abs f < half, then round r = truncate r, " <>
                  "where (_, f) = properFraction r") propRoundLow,
    testProperty ("if abs f > half, then abs (round r) = abs (truncate r) + 1, " <>
                  "where (_, f) = properFraction r") propRoundHigh
    ]
  ]

-- Properties

propEqRefl :: Property
propEqRefl = property $ do
  x <- forAllWith ppShow genRational
  (x Plutus.== x) === True

propEqSymm :: Property
propEqSymm = property $ do
  ent <- forAllWith ppShow (entangled genRational)
  cover 45 "identical" . isDefinitelyIdentical $ ent
  cover 45 "possibly different" . not . isDefinitelyIdentical $ ent
  let (x, y) = collapse ent
  if x Plutus.== y
  then (y Plutus.== x) === True
  else success

propEqTrans :: Property
propEqTrans = property $ do
  ent3 <- forAllWith ppShow (entangled3 genRational)
  cover 45 "identical" . isDefinitelyIdentical3 $ ent3
  cover 45 "possibly different" . not . isDefinitelyIdentical3 $ ent3
  let (x, y, z) = collapse3 ent3
  if x Plutus.== y && y Plutus.== z
  then (x Plutus.== z) === True
  else success

propEqSub :: Property
propEqSub = property $ do
  f <- forAllFn . fnWith varyRational $ genInteger
  ent <- forAllWith ppShow (entangled genRational)
  cover 45 "identical" . isDefinitelyIdentical $ ent
  cover 45 "possibly different" . not . isDefinitelyIdentical $ ent
  let (x, y) = collapse ent
  if x Plutus.== y
  then f x === f y
  else success

propOrdRefl :: Property
propOrdRefl = property $ do
  x <- forAllWith ppShow genRational
  (x Plutus.<= x) === True

propOrdAntiSymm :: Property
propOrdAntiSymm = property $ do
  ent <- forAllWith ppShow (entangled genRational)
  cover 45 "identical" . isDefinitelyIdentical $ ent
  cover 45 "possibly different" . not . isDefinitelyIdentical $ ent
  let (x, y) = collapse ent
  if x Plutus.<= y && y Plutus.<= x
  then x === y
  else success

propOrdTrans :: Property
propOrdTrans = property $ do
  ent3 <- forAllWith ppShow (entangled3 genRational)
  cover 45 "identical" . isDefinitelyIdentical3 $ ent3
  cover 45 "possibly different" . not . isDefinitelyIdentical3 $ ent3
  let (x, y, z) = collapse3 ent3
  if x Plutus.<= y && y Plutus.<= z
  then (x Plutus.<= z) === True
  else success

propOrdCompare :: Property
propOrdCompare = property $ do
  ent <- forAllWith ppShow (entangled genRational)
  cover 45 "identical" . isDefinitelyIdentical $ ent
  cover 45 "possibly different" . not . isDefinitelyIdentical $ ent
  let (x, y) = collapse ent
  if x Plutus.== y
  then Plutus.compare x y === Plutus.EQ
  else Plutus.compare x y /== Plutus.EQ

propPlusComm :: Property
propPlusComm = property $ do
  x <- forAllWith ppShow genRational
  y <- forAllWith ppShow genRational
  x Plutus.+ y === y Plutus.+ x

propPlusAssoc :: Property
propPlusAssoc = property $ do
  x <- forAllWith ppShow genRational
  y <- forAllWith ppShow genRational
  z <- forAllWith ppShow genRational
  (x Plutus.+ y) Plutus.+ z === x Plutus.+ (y Plutus.+ z)

propZeroId :: Property
propZeroId = property $ do
  x <- forAllWith ppShow genRational
  x Plutus.+ Plutus.zero === x

propMinusCancel :: Property
propMinusCancel = property $ do
  x <- forAllWith ppShow genRational
  x Plutus.- x === Plutus.zero

propTimesAssoc :: Property
propTimesAssoc = property $ do
  x <- forAllWith ppShow genRational
  y <- forAllWith ppShow genRational
  z <- forAllWith ppShow genRational
  (x Plutus.* y) Plutus.* z === x Plutus.* (y Plutus.* z)

propOneLeftId :: Property
propOneLeftId = property $ do
  x <- forAllWith ppShow genRational
  Plutus.one Plutus.* x === x

propOneRightId :: Property
propOneRightId = property $ do
  x <- forAllWith ppShow genRational
  x Plutus.* Plutus.one === x

propZeroLeftAnnih :: Property
propZeroLeftAnnih = property $ do
  x <- forAllWith ppShow genRational
  Plutus.zero Plutus.* x === Plutus.zero

propZeroRightAnnih :: Property
propZeroRightAnnih = property $ do
  x <- forAllWith ppShow genRational
  x Plutus.* Plutus.zero === Plutus.zero

propTimesLeftDistPlus :: Property
propTimesLeftDistPlus = property $ do
  x <- forAllWith ppShow genRational
  y <- forAllWith ppShow genRational
  z <- forAllWith ppShow genRational
  x Plutus.* (y Plutus.+ z) === (x Plutus.* y) Plutus.+ (x Plutus.* z)

propTimesRightDistPlus :: Property
propTimesRightDistPlus = property $ do
  x <- forAllWith ppShow genRational
  y <- forAllWith ppShow genRational
  z <- forAllWith ppShow genRational
  (x Plutus.+ y) Plutus.* z === (x Plutus.* z) Plutus.+ (y Plutus.* z)

propScaleOne :: Property
propScaleOne = property $ do
  x <- forAllWith ppShow genRational
  Plutus.scale Plutus.one x === x

propScaleDistPlus :: Property
propScaleDistPlus = property $ do
  x <- forAllWith ppShow genInteger
  y <- forAllWith ppShow genRational
  z <- forAllWith ppShow genRational
  Plutus.scale x (y Plutus.+ z) === Plutus.scale x y Plutus.+ Plutus.scale x z

propScaleTimes :: Property
propScaleTimes = property $ do
  x <- forAllWith ppShow genInteger
  y <- forAllWith ppShow genInteger
  r <- forAllWith ppShow genRational
  Plutus.scale x (Plutus.scale y r) === Plutus.scale (x Plutus.* y) r

propUnsafeIsData :: Property
propUnsafeIsData = property $ do
  x <- forAllWith ppShow genRational
  (unsafeFromBuiltinData . toBuiltinData $ x) === x

propZeroDenom :: Property
propZeroDenom = property $ do
  x <- forAllWith ppShow genInteger
  Ratio.ratio x Plutus.zero === Nothing

propOneDenom :: Property
propOneDenom = property $ do
  x <- forAllWith ppShow genInteger
  Ratio.ratio x Plutus.one === (Just . Ratio.fromInteger $ x)

propConstructionAgreement :: Property
propConstructionAgreement = property $ do
  n <- forAllWith ppShow genInteger
  d <- forAllWith ppShow . Gen.filter (/= 0) $ genInteger
  Ratio.ratio n d === (Just . Ratio.unsafeRatio n $ d)

propFromIntegerNum :: Property
propFromIntegerNum = property $ do
  x <- forAllWith ppShow genInteger
  let r = Ratio.fromInteger x
  Ratio.numerator r === x

propFromIntegerDen :: Property
propFromIntegerDen = property $ do
  x <- forAllWith ppShow genInteger
  let r = Ratio.fromInteger x
  Ratio.denominator r === Plutus.one

propPosDen :: Property
propPosDen = property $ do
  r <- forAllWith ppShow genRational
  assert (Ratio.denominator r Plutus.>= Plutus.one)

propDoubleNeg :: Property
propDoubleNeg = property $ do
  r <- forAllWith ppShow genRational
  (Ratio.negate . Ratio.negate $ r) === r

propAbs :: Property
propAbs = property $ do
  r <- forAllWith ppShow genRational
  assert (Ratio.abs r >= Plutus.zero)

propIsDataRound :: Property
propIsDataRound = property $ do
  r <- forAllWith ppShow genRational
  tripping r toBuiltinData fromBuiltinData

propIsJSONRound :: Property
propIsJSONRound = property $ do
  r <- forAllWith ppShow genRational
  tripping r encode decode

propRatioScale :: Property
propRatioScale = property $ do
  x <- forAllWith ppShow genInteger
  y <- forAllWith ppShow genInteger
  z <- forAllWith ppShow . Gen.filter (/= Plutus.zero) $ genInteger
  Ratio.ratio x y === Ratio.ratio (x Plutus.* z) (y Plutus.* z)

propRatioSelf :: Property
propRatioSelf = property $ do
  x <- forAllWith ppShow . Gen.filter (/= Plutus.zero) $ genInteger
  Ratio.ratio x x === Just Plutus.one

propRatioSign :: Property
propRatioSign = property $ do
  (n, d) <- forAllWith ppShow go
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

propNumeratorScale :: Property
propNumeratorScale = property $ do
  r <- forAllWith ppShow genRational
  Ratio.numerator r === (Ratio.numerator . Plutus.scale (Ratio.denominator r) $ r)

propRecipSelf :: Property
propRecipSelf = property $ do
  r <- forAllWith ppShow . Gen.filter (/= Plutus.zero) $ genRational
  Ratio.recip r Plutus.* r === Plutus.one

propAbsTimes :: Property
propAbsTimes = property $ do
  r <- forAllWith ppShow genRational
  r' <- forAllWith ppShow genRational
  Ratio.abs r Plutus.* Ratio.abs r' === Ratio.abs (r Plutus.* r')

propProperFrac :: Property
propProperFrac = property $ do
  r <- forAllWith ppShow genRational
  let (n, f) = Ratio.properFraction r
  r === Ratio.fromInteger n Plutus.+ f

propProperFracAbs :: Property
propProperFracAbs = property $ do
  r <- forAllWith ppShow genRational
  let (_, f) = Ratio.properFraction r
  assert (Ratio.abs f Plutus.< Plutus.one)

propProperFracSigns :: Property
propProperFracSigns = property $ do
  r <- forAllWith ppShow go
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
      (genN, genD) <- Gen.element [(genIntegerPos, negate <$> genIntegerPos),
                                   (negate <$> genIntegerPos, genIntegerPos)]
      Ratio.unsafeRatio <$> genN <*> genD

propAbsRound :: Property
propAbsRound = property $ do
  r <- forAllWith ppShow genRational
  let rounded = Ratio.round r
  let (n, _) = Ratio.properFraction r
  assert (Plutus.abs rounded Plutus.>= Plutus.abs n)

propRoundHalf :: Property
propRoundHalf = property $ do
  (n, f) <- forAllWith ppShow go
  let r = Ratio.fromInteger n Plutus.+ f
  let rounded = Ratio.round r
  case (signum n, even n) of
    (-1, False) -> rounded === n Plutus.- Plutus.one
    (-1, True)  -> rounded === n
    (0, _)      -> rounded === Plutus.zero
    (1, False)  -> rounded === n Plutus.+ Plutus.one
    _           -> rounded === n
  where
    go :: Gen (Integer, Plutus.Rational)
    go = do
      n <- genInteger
      f <- case signum n of
            (-1) -> pure . Ratio.negate $ Ratio.half
            0    -> Gen.element [Ratio.half, Ratio.negate Ratio.half]
            _    -> pure Ratio.half
      pure (n, f)

propRoundLow :: Property
propRoundLow = property $ do
  (n, f) <- forAllWith ppShow go
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
  (n, f) <- forAllWith ppShow go
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

-- Helpers

instance Arg Plutus.Rational where
  build = via separate (uncurry Ratio.unsafeRatio)

varyRational :: CoGen Plutus.Rational
varyRational = contramap separate vary

separate :: Plutus.Rational -> (Plutus.Integer, Plutus.Integer)
separate r = (Ratio.numerator r, Ratio.denominator r)

genRational :: Gen Plutus.Rational
genRational = do
  num <- genInteger
  den <- Gen.integral . Range.linearFrom 100 0 $ 200
  pure . Ratio.unsafeRatio num $ den

genInteger :: Gen Integer
genInteger = Gen.integral . Range.linearFrom 0 (-100) $ 100

genIntegerPos :: Gen Integer
genIntegerPos = Gen.integral . Range.linearFrom 50 1 $ 100

-- This is a hack to ensure coverage.
data Entangled (a :: Type) =
  Identical a |
  Regular a a
  deriving stock (Eq, Show)

collapse :: Entangled a -> (a, a)
collapse = \case
  Identical x -> (x, x)
  Regular x y -> (x, y)

isDefinitelyIdentical :: Entangled a -> Bool
isDefinitelyIdentical = \case
  Identical _ -> True
  Regular _ _ -> False

entangled :: forall (a :: Type) . Gen a -> Gen (Entangled a)
entangled gen = Gen.choice [Identical <$> gen, Regular <$> gen <*> gen]

-- Similar, but for triples.
data Entangled3 (a :: Type) =
  Identical3 a |
  Regular3 a a a
  deriving stock (Eq, Show)

collapse3 :: Entangled3 a -> (a, a, a)
collapse3 = \case
  Identical3 x   -> (x, x, x)
  Regular3 x y z -> (x, y, z)

isDefinitelyIdentical3 :: Entangled3 a -> Bool
isDefinitelyIdentical3 = \case
  Identical3 _ -> True
  Regular3{}   -> False

entangled3 :: forall (a :: Type) . Gen a -> Gen (Entangled3 a)
entangled3 gen = Gen.choice [Identical3 <$> gen, Regular3 <$> gen <*> gen <*> gen]
