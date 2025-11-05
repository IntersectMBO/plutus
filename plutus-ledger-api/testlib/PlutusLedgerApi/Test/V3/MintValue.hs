{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusLedgerApi.Test.V3.MintValue where

import Data.Coerce (coerce)
import PlutusCore.Generators.QuickCheck.Builtin
import PlutusCore.Generators.QuickCheck.Split (multiSplit0)
import PlutusCore.Value qualified as Value
import PlutusLedgerApi.V3
import PlutusLedgerApi.V3.MintValue (MintValue (..))
import PlutusTx.AssocMap qualified as Map
import PlutusTx.List qualified as List
import Test.QuickCheck (Arbitrary (..))

instance Arbitrary MintValue where
  arbitrary = do
    -- Generate values for all of the 'TokenName's in the final 'MintValue'
    -- and split them into a list of lists.
    faceValues <- multiSplit0 0.2 . map unQuantity =<< arbitrary
    -- Generate 'TokenName's and 'CurrencySymbol's.
    currencies <-
      uniqueNames (CurrencySymbol . toBuiltin . Value.unK)
        =<< traverse (uniqueNames (TokenName . toBuiltin . Value.unK)) faceValues
    pure $ listsToMintValue currencies

  shrink =
    map listsToMintValue
      . coerce
        (shrink @[(NoArbitrary CurrencySymbol, [(NoArbitrary TokenName, Integer)])])
      . mintValueToLists

-- | Convert a list representation of a 'MintValue' to the 'MintValue'.
listsToMintValue :: [(CurrencySymbol, [(TokenName, Integer)])] -> MintValue
listsToMintValue = coerce . Map.unsafeFromList . List.map (fmap Map.unsafeFromList)

-- | Convert a 'MintValue' to its list representation.
mintValueToLists :: MintValue -> [(CurrencySymbol, [(TokenName, Integer)])]
mintValueToLists = List.map (fmap Map.toList) . Map.toList . coerce

newtype Quantity = Quantity {unQuantity :: Integer}
  deriving newtype (Arbitrary, Show)
