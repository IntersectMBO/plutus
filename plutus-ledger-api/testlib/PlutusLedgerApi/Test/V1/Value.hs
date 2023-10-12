{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module PlutusLedgerApi.Test.V1.Value where

import PlutusLedgerApi.V1
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.List qualified as ListTx

import PlutusCore.Generators.QuickCheck.Utils (multiSplit, uniqueVectorOf)

import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Char8 qualified as BS8
import Data.Coerce
import Test.QuickCheck

listsToValue :: [(CurrencySymbol, [(TokenName, Integer)])] -> Value
listsToValue = Value . AssocMap.fromList . ListTx.map (fmap AssocMap.fromList)

valueToLists :: Value -> [(CurrencySymbol, [(TokenName, Integer)])]
valueToLists = ListTx.map (fmap AssocMap.toList) . AssocMap.toList . getValue

-- >>> map (\i -> (i, toNameCandidatesNumber i)) [1..13]
-- [(1,6),(2,6),(3,6),(4,8),(5,11),(6,14),(7,18),(8,22),(9,27),(10,31),(11,36),(12,41),(13,46)]
toNameCandidatesNumber :: Int -> Int
toNameCandidatesNumber i = max 6 . floor @Double $ fromIntegral i ** 1.5

genShortHex :: Int -> Gen BuiltinByteString
genShortHex i =
    toBuiltin . Base16.encode . BS8.pack . show <$> elements [0 .. toNameCandidatesNumber i]

uniqueNames :: Eq name => (BuiltinByteString -> name) -> [b] -> Gen [(name, b)]
uniqueNames wrap ys = do
    let len = length ys
    xs <- uniqueVectorOf len $ wrap <$> genShortHex len
    pure $ zip xs ys

newtype FaceValue = FaceValue
    { unFaceValue :: Integer
    }

instance Arbitrary FaceValue where
    -- We want to generate zeroes often, because there's a lot of corner cases associated with them
    -- and all non-zero numbers are handled pretty much the same anyway, so there isn't much point
    -- in diversifying them as much as possible.
    arbitrary = frequency
        [ (2, pure $ FaceValue 0)
        , (1, FaceValue . fromIntegral <$> arbitrary @Int)
        ]

newtype NoArbitrary a = NoArbitrary
    { unNoArbitrary :: a
    }

instance Arbitrary (NoArbitrary a) where
    arbitrary = error "No such 'Arbitrary' instance"

instance Arbitrary Value where
    arbitrary = do
        faceValues <- fmap (map getNonEmpty) . multiSplit . map unFaceValue =<< arbitrary
        currencies <- uniqueNames CurrencySymbol =<< traverse (uniqueNames TokenName) faceValues
        pure $ listsToValue currencies

    shrink
        = map listsToValue
        . coerce (shrink @[(NoArbitrary CurrencySymbol, [(NoArbitrary TokenName, Integer)])])
        . valueToLists
