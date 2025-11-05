{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module PlutusLedgerApi.Test.V1.Value where

import PlutusLedgerApi.V1
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.List qualified as ListTx

import PlutusCore.Generators.QuickCheck.Builtin
import PlutusCore.Generators.QuickCheck.Utils (multiSplit0)
import PlutusCore.Value qualified as PLC

import Data.Bifunctor
import Data.Coerce
import Data.Map.Strict qualified as Map
import Test.QuickCheck

-- | Convert a list representation of a 'Value' to the 'Value'.
listsToValue :: [(CurrencySymbol, [(TokenName, Integer)])] -> Value
listsToValue = Value . AssocMap.unsafeFromList . ListTx.map (fmap AssocMap.unsafeFromList)

-- | Convert a 'Value' to its list representation.
valueToLists :: Value -> [(CurrencySymbol, [(TokenName, Integer)])]
valueToLists = ListTx.map (fmap AssocMap.toList) . AssocMap.toList . getValue

-- | The value of a 'TokenName' in a 'Value'.
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

instance Arbitrary Value where
    arbitrary = do
        -- Generate values for all of the 'TokenName's in the final 'Value' and split them into a
        -- list of lists.
        faceValues <- multiSplit0 0.2 . map unFaceValue =<< arbitrary
        -- Generate 'TokenName's and 'CurrencySymbol's.
        currencies <- uniqueNames (CurrencySymbol . toBuiltin . PLC.unK) =<<
            traverse (uniqueNames (TokenName . toBuiltin . PLC.unK)) faceValues
        pure $ listsToValue currencies

    shrink
        = map listsToValue
        . coerce (shrink @[(NoArbitrary CurrencySymbol, [(NoArbitrary TokenName, Integer)])])
        . valueToLists

valueFromBuiltin :: PLC.Value -> Value
valueFromBuiltin =
  listsToValue
    . fmap (bimap (CurrencySymbol . toBuiltin . PLC.unK) inner)
    . Map.toList
    . PLC.unpack
 where
  inner = fmap (bimap (TokenName . toBuiltin . PLC.unK) PLC.unQuantity) . Map.toList
