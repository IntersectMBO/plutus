module Suites.Laws.Serialization (serializationLaws) where

import Data.Aeson (decode, encode)
import Hedgehog (Property, property, tripping, (===))
import PlutusTx.IsData.Class (fromBuiltinData, toBuiltinData, unsafeFromBuiltinData)
import Prelude
import Suites.Laws.Helpers (forAllWithPP, genRational)
import Test.Tasty (TestTree)
import Test.Tasty.Hedgehog (testProperty)

serializationLaws :: [TestTree]
serializationLaws = [
  testProperty "FromBuiltinData-ToBuiltinData roundtrip" propIsDataRound,
  testProperty "unsafeFromBuiltinData . toBuiltinData = id" propUnsafeIsData,
  testProperty "FromJSON-ToJSON roundtrip" propIsJSONRound
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
