{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusLedgerApi.Test.V3.Data.MintValue where

import Data.Coerce (coerce)
import PlutusCore.Generators.QuickCheck.Split (multiSplit0)
import PlutusLedgerApi.Test.V1.Data.Value (NoArbitrary (..), uniqueNames)
import PlutusLedgerApi.V1.Data.Value (CurrencySymbol (..), TokenName (..))
import PlutusLedgerApi.V3.Data.MintValue (MintValue (..))
import PlutusTx.Data.AssocMap qualified as Map
import PlutusTx.List qualified as List
import Test.QuickCheck (Arbitrary (..))

instance Arbitrary MintValue where
  arbitrary = do
    -- Generate values for all of the 'TokenName's in the final 'MintValue'
    -- and split them into a list of lists.
    faceValues <- multiSplit0 0.2 . map unQuantity =<< arbitrary
    -- Generate 'TokenName's and 'CurrencySymbol's.
    currencies <-
      uniqueNames CurrencySymbol
        =<< traverse (uniqueNames TokenName) faceValues
    pure $ listsToMintValue currencies

  shrink =
    map listsToMintValue
      . coerce
        (shrink @[(NoArbitrary CurrencySymbol, [(NoArbitrary TokenName, Integer)])])
      . mintValueToLists

-- | Convert a list representation of a 'MintValue' to the 'MintValue'.
listsToMintValue :: [(CurrencySymbol, [(TokenName, Integer)])] -> MintValue
listsToMintValue =
  coerce . Map.unsafeFromSOPList . List.map (fmap (Map.unsafeFromSOPList))

-- | Convert a 'MintValue' to its list representation.
mintValueToLists :: MintValue -> [(CurrencySymbol, [(TokenName, Integer)])]
mintValueToLists = List.map (fmap Map.toSOPList) . Map.toSOPList . coerce

newtype Quantity = Quantity {unQuantity :: Integer}
  deriving newtype (Arbitrary, Show)
