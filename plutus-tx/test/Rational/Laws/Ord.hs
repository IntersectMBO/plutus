-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}

module Rational.Laws.Ord (ordLaws) where

import Hedgehog (Property, PropertyT, property, success, (/==), (===))
import PlutusTx.Prelude qualified as Plutus
import Rational.Laws.Helpers
  ( forAllWithPP
  , genRational
  , normalAndEquivalentTo
  , testEntangled
  , testEntangled3
  )
import Test.Tasty (TestTree)
import Test.Tasty.Hedgehog (testPropertyNamed)
import Prelude

ordLaws :: [TestTree]
ordLaws =
  [ testPropertyNamed "<= is reflexive" "propOrdRefl" propOrdRefl
  , testEntangled "<= is anti-symmetric" genRational propOrdAntiSymm
  , testEntangled3 "<= is transitive" genRational propOrdTrans
  , testEntangled "== implies EQ" genRational propOrdCompare
  ]

-- Helpers

propOrdRefl :: Property
propOrdRefl = property $ do
  x <- forAllWithPP genRational
  (x Plutus.<= x) === True

propOrdAntiSymm :: Plutus.Rational -> Plutus.Rational -> PropertyT IO ()
propOrdAntiSymm x y =
  if x Plutus.<= y && y Plutus.<= x
    then x `normalAndEquivalentTo` y
    else success

propOrdTrans :: Plutus.Rational -> Plutus.Rational -> Plutus.Rational -> PropertyT IO ()
propOrdTrans x y z =
  if x Plutus.<= y && y Plutus.<= z
    then (x Plutus.<= z) === True
    else success

propOrdCompare :: Plutus.Rational -> Plutus.Rational -> PropertyT IO ()
propOrdCompare x y =
  if x Plutus.== y
    then Plutus.compare x y === Plutus.EQ
    else Plutus.compare x y /== Plutus.EQ
