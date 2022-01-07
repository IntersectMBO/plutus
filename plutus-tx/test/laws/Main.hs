{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# OPTIONS_GHC -Wno-orphans #-} -- We need Arg for hedgehog-fn

module Main (main) where

import Prelude

import Data.Functor.Contravariant (contramap)
import Data.Kind (Type)
import Hedgehog (Gen, Property, cover, forAllWith, property, success, (===))
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
  Identical3 _   -> True
  Regular3 _ _ _ -> False

entangled3 :: forall (a :: Type) . Gen a -> Gen (Entangled3 a)
entangled3 gen = Gen.choice [Identical3 <$> gen, Regular3 <$> gen <*> gen <*> gen]
