{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module PlutusLedgerApi.Test.V1.Data.Value where

-- TODO: import a new PlutusLedgerApi.Data.V1 module instead
import PlutusLedgerApi.V1.Data.Value
import PlutusTx.Builtins hiding (error)

--
import PlutusTx.Data.AssocMap qualified as AssocMap
import PlutusTx.List qualified as ListTx

import PlutusCore.Generators.QuickCheck.Utils (multiSplit0, uniqueVectorOf)

import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Char8 qualified as BS8
import Data.Coerce
import Test.QuickCheck

-- | Convert a list representation of a 'Value' to the 'Value'.
listsToValue :: [(CurrencySymbol, [(TokenName, Integer)])] -> Value
listsToValue = Value . AssocMap.unsafeFromSOPList . ListTx.map (fmap AssocMap.unsafeFromSOPList)

-- | Convert a 'Value' to its list representation.
valueToLists :: Value -> [(CurrencySymbol, [(TokenName, Integer)])]
valueToLists = ListTx.map (fmap AssocMap.toSOPList) . AssocMap.toSOPList . getValue

{-| Return how many candidates to randomly choose from to fill the given number of cells. For
example, if we only need to fill a single cell, we choose from 6 different candidates, and if we
need to fill 5 cells, we choose from 11 candidates.

>>> map (\i -> (i, toCellCandidatesNumber i)) [1..13]
[(1,6),(2,6),(3,6),(4,8),(5,11),(6,14),(7,18),(8,22),(9,27),(10,31),(11,36),(12,41),(13,46)] -}
toCellCandidatesNumber :: Int -> Int
toCellCandidatesNumber i = max 6 . floor @Double $ fromIntegral i ** 1.5

{-| Generate a 'BuiltinByteString' by picking one of the predetermined ones, given a number of
cells to fill (see 'toCellCandidatesNumber'). The idea is that we want to occasionally generate
the same 'CurrencySymbol' or 'TokenName' for different 'Value's to have decent test coverage,
hence to make name clashing more likely we pick from a predetermined set of
'BuiltinByteString's. Otherwise the chance of generating the same 'BuiltinByteString' for two
different 'Value's would be virtually zero. -}
genShortHex :: Int -> Gen BuiltinByteString
genShortHex i =
  toBuiltin . Base16.encode . BS8.pack . show <$> elements [0 .. toCellCandidatesNumber i]

{-| Annotate each element of the give list with a @name@, given a function turning
'BuiltinByteString' into names. -}
uniqueNames :: Eq name => (BuiltinByteString -> name) -> [b] -> Gen [(name, b)]
uniqueNames wrap ys = do
  let len = length ys
  -- We always generate unique 'CurrencySymbol's within a single 'Value' and 'TokenName' within a
  -- single 'CurrencySymbol', because functions over 'Value' don't handle duplicated names anyway.
  -- Note that we can generate the same 'TokenName' within different 'CurrencySymbol's within the
  -- same 'Value'.
  xs <- uniqueVectorOf len $ wrap <$> genShortHex len
  pure $ zip xs ys

-- | The value of a 'TokenName' in a 'Value'.
newtype FaceValue = FaceValue
  { unFaceValue :: Integer
  }

instance Arbitrary FaceValue where
  -- We want to generate zeroes often, because there's a lot of corner cases associated with them
  -- and all non-zero numbers are handled pretty much the same anyway, so there isn't much point
  -- in diversifying them as much as possible.
  arbitrary =
    frequency
      [ (2, pure $ FaceValue 0)
      , (1, FaceValue . fromIntegral <$> arbitrary @Int)
      ]

{-| A wrapper for satisfying an @Arbitrary a@ constraint without implementing an 'Arbitrary'
instance for @a@. -}
newtype NoArbitrary a = NoArbitrary
  { unNoArbitrary :: a
  }

-- | 'arbitrary' throws, 'shrink' neither throws nor shrinks.
instance Arbitrary (NoArbitrary a) where
  arbitrary = error "No such 'Arbitrary' instance"
  shrink _ = []

instance Arbitrary Value where
  arbitrary = do
    -- Generate values for all of the 'TokenName's in the final 'Value' and split them into a
    -- list of lists.
    faceValues <- multiSplit0 0.2 . map unFaceValue =<< arbitrary
    -- Generate 'TokenName's and 'CurrencySymbol's.
    currencies <- uniqueNames CurrencySymbol =<< traverse (uniqueNames TokenName) faceValues
    pure $ listsToValue currencies

  shrink =
    map listsToValue
      . coerce (shrink @[(NoArbitrary CurrencySymbol, [(NoArbitrary TokenName, Integer)])])
      . valueToLists
