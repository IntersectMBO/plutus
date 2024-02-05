-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}

module Rational.Laws.Serialization (serializationLaws) where

import Data.Aeson (decode, encode)
import Hedgehog (Property, property, tripping, (===))
import PlutusTx.IsData.Class (fromBuiltinData, toBuiltinData, unsafeFromBuiltinData)
import Rational.Laws.Helpers (forAllWithPP, genRational)
import Test.Tasty (TestTree)
import Test.Tasty.Hedgehog (testPropertyNamed)
import Prelude

serializationLaws :: [TestTree]
serializationLaws =
  [ testPropertyNamed "FromBuiltinData-ToBuiltinData roundtrip" "propIsDataRound" propIsDataRound
  , testPropertyNamed "unsafeFromBuiltinData . toBuiltinData = id" "propUnsafeIsData" propUnsafeIsData
  , testPropertyNamed "FromJSON-ToJSON roundtrip" "propIsJSONRound" propIsJSONRound
  ]

-- Helpers

propIsDataRound :: Property
propIsDataRound = property $ do
  r <- forAllWithPP genRational
  tripping r toBuiltinData fromBuiltinData

propUnsafeIsData :: Property
propUnsafeIsData = property $ do
  x <- forAllWithPP genRational
  (unsafeFromBuiltinData . toBuiltinData $ x) === x

propIsJSONRound :: Property
propIsJSONRound = property $ do
  r <- forAllWithPP genRational
  tripping r encode decode
