-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}

module Rational.Laws.Eq (eqLaws) where

import Hedgehog (Property, PropertyT, property, success, (===))
import Hedgehog.Function (fnWith, forAllFn)
import PlutusTx.Prelude qualified as Plutus
import Rational.Laws.Helpers
  ( forAllWithPP
  , genInteger
  , genRational
  , testEntangled
  , testEntangled3
  , varyRational
  )
import Test.Tasty (TestTree)
import Test.Tasty.Hedgehog (testPropertyNamed)
import Prelude

eqLaws :: [TestTree]
eqLaws =
  [ testPropertyNamed "== is reflexive" "propEqRefl" propEqRefl
  , testEntangled "== is symmetric" genRational propEqSymm
  , testEntangled3 "== is transitive" genRational propEqTrans
  , testEntangled "== implies substitution" genRational propEqSub
  ]

-- Helpers

propEqRefl :: Property
propEqRefl = property $ do
  x <- forAllWithPP genRational
  (x Plutus.== x) === True

propEqSymm :: Plutus.Rational -> Plutus.Rational -> PropertyT IO ()
propEqSymm x y = if x Plutus.== y then (y Plutus.== x) === True else success

propEqTrans :: Plutus.Rational -> Plutus.Rational -> Plutus.Rational -> PropertyT IO ()
propEqTrans x y z =
  if x Plutus.== y && y Plutus.== z
    then (x Plutus.== z) === True
    else success

propEqSub :: Plutus.Rational -> Plutus.Rational -> PropertyT IO ()
propEqSub x y = do
  f <- forAllFn . fnWith varyRational $ genInteger
  if x Plutus.== y
    then f x === f y
    else success
