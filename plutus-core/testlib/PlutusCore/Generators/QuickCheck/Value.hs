{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module PlutusCore.Generators.QuickCheck.Value where

import Data.ByteString (ByteString)
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Char8 qualified as BC
import Data.Coerce
import PlutusCore.Generators.QuickCheck.Utils (multiSplit0, uniqueVectorOf)
import PlutusCore.Value (Value)
import PlutusCore.Value qualified as Value
import System.Random
import Test.QuickCheck

{-| Return how many candidates to randomly choose from to fill the given number of cells. For
example, if we only need to fill a single cell, we choose from 6 different candidates, and if we
need to fill 5 cells, we choose from 11 candidates.

>>> map (\i -> (i, toCellCandidatesNumber i)) [1..13]
[(1,6),(2,6),(3,6),(4,8),(5,11),(6,14),(7,18),(8,22),(9,27),(10,31),(11,36),(12,41),(13,46)]
-}
toCellCandidatesNumber :: Int -> Int
toCellCandidatesNumber i = max 6 . floor @Double $ fromIntegral i ** 1.5

{-| Generate a 'ByteString' by picking one of the predetermined ones, given a number of
cells to fill (see 'toCellCandidatesNumber'). The idea is that we want to occasionally generate
the same 'CurrencySymbol' or 'TokenName' for different 'Value's to have decent test coverage,
hence to make name clashing more likely we pick from a predetermined set of
'ByteString's. Otherwise the chance of generating the same 'ByteString' for two
different 'Value's would be virtually zero.
-}
genShortHex :: Int -> Gen ByteString
genShortHex i =
  Base16.encode . BC.pack . show <$> elements [0 .. toCellCandidatesNumber i]

{-| Annotate each element of the give list with a @name@, given a function turning
'ByteString' into names.
-}
uniqueNames :: (Eq name) => (ByteString -> name) -> [b] -> Gen [(name, b)]
uniqueNames wrap ys = do
  let len = length ys
  -- We always generate unique 'CurrencySymbol's within a single 'Value' and 'TokenName' within a
  -- single 'CurrencySymbol', because functions over 'Value' don't handle duplicated names anyway.
  -- Note that we can generate the same 'TokenName' within different 'CurrencySymbol's within the
  -- same 'Value'.
  xs <- uniqueVectorOf len $ wrap <$> genShortHex len
  pure $ zip xs ys

newtype ValueAmount = ValueAmount {unValueAmount :: Integer}
  deriving newtype (Num, Random)

instance Arbitrary ValueAmount where
  arbitrary =
    frequency
      [ -- favor small amounts, so we hit interesting cases like `a + (-a)` more often.
        (5, choose (-100, 100))
      , (1, arbitrary)
      ]

{-| A wrapper for satisfying an @Arbitrary a@ constraint without implementing an 'Arbitrary'
instance for @a@.
-}
newtype NoArbitrary a = NoArbitrary
  { unNoArbitrary :: a
  }

-- | 'arbitrary' throws, 'shrink' neither throws nor shrinks.
instance Arbitrary (NoArbitrary a) where
  arbitrary = error "arbitrary @(NoArbitrary a)"
  shrink _ = []

instance Arbitrary Value where
  arbitrary = do
    -- Generate values for all of the 'TokenName's in the final 'Value' and split them into a
    -- list of lists.
    amts <- multiSplit0 0.2 . map unValueAmount =<< arbitrary
    -- Generate 'TokenName's and 'CurrencySymbol's.
    currencies <- uniqueNames id =<< traverse (uniqueNames id) amts
    pure $ Value.fromList currencies

  shrink =
    map Value.fromList
      . coerce (shrink @[(NoArbitrary ByteString, [(NoArbitrary ByteString, Integer)])])
      . Value.toList
