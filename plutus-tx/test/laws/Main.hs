{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# OPTIONS_GHC -Wno-orphans #-} -- We need an Arg instance for hedgehog-fn

module Main (main) where

import Prelude

import Data.Functor.Contravariant (contramap)
import Data.Kind (Type)
import Hedgehog (Gen, Property, cover, forAllWith, property, success, (/==), (===))
import Hedgehog.Function (Arg (build), CoGen, fnWith, forAllFn, vary, via)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusTx.Prelude qualified as Plutus
import PlutusTx.Ratio as Ratio
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
    testProperty "x - x = zero" propMinusCancel
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
  Plutus.scale x (y Plutus.+ z) === (Plutus.scale x y) Plutus.+ (Plutus.scale x z)

propScaleTimes :: Property
propScaleTimes = property $ do
  x <- forAllWith ppShow genInteger
  y <- forAllWith ppShow genInteger
  r <- forAllWith ppShow genRational
  Plutus.scale x (Plutus.scale y r) === Plutus.scale (x Plutus.* y) r

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
