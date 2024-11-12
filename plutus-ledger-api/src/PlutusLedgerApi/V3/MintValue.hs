{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-unbox-small-strict-fields #-}
{-# OPTIONS_GHC -fno-unbox-strict-fields #-}

module PlutusLedgerApi.V3.MintValue
  ( MintValue (..) -- Constructor is exported for testing
  , emptyMintValue
  , mintValueToMap
  , mintValueMinted
  , mintValueBurned
  )
where

import PlutusTx.Prelude

import Control.DeepSeq (NFData)
import Data.Data (Data, Typeable)
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Value (CurrencySymbol, TokenName, Value (..))
import PlutusTx (FromData (..), ToData (..), UnsafeFromData (..))
import PlutusTx.AssocMap (Map)
import PlutusTx.AssocMap qualified as Map
import PlutusTx.Blueprint.Class (HasBlueprintSchema (..))
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition (..), definitionIdFromType,
                                      definitionRef)
import PlutusTx.Blueprint.Schema (MapSchema (..), Schema (..))
import PlutusTx.Blueprint.Schema.Annotation (emptySchemaInfo, title)
import PlutusTx.Lift (makeLift)
import Prelude qualified as Haskell
import Prettyprinter (Pretty)
import Prettyprinter.Extras (PrettyShow (PrettyShow))

{- Note [MintValue vs Value]

'MintValue' differs conceptually from 'Value' in how negative quantities are interpreted:

In 'MintValue', negative quantities are interpreted as assets being burned. For 'Value',
negative quantities are either don't make sense (e.g. in a transaction output) or interpreted
as a negative balance.

We want to distinguish these at the type level to avoid using 'MintValue' where 'Value' is assumed.
Users should project 'MintValue' into 'Value' using 'mintValueMinted' or 'mintValueBurned'.
-}

-- | A 'MintValue' represents assets that are minted and burned in a transaction.
newtype MintValue = UnsafeMintValue (Map CurrencySymbol (Map TokenName Integer))
  deriving stock (Generic, Data, Typeable, Haskell.Show)
  deriving anyclass (NFData)
  deriving newtype (ToData, FromData, UnsafeFromData)
  deriving (Pretty) via (PrettyShow MintValue)

instance Haskell.Eq MintValue where
  l == r = mintValueMinted l == mintValueMinted r && mintValueBurned l == mintValueBurned r

instance HasBlueprintDefinition MintValue where
  type Unroll MintValue = '[MintValue, CurrencySymbol, TokenName, Integer]
  definitionId = definitionIdFromType @MintValue

instance HasBlueprintSchema MintValue referencedTypes where
  {-# INLINEABLE schema #-}
  schema =
    SchemaMap
      emptySchemaInfo{title = Just "MintValue"}
      MkMapSchema
        { keySchema = definitionRef @CurrencySymbol
        , valueSchema =
            SchemaMap
              emptySchemaInfo
              MkMapSchema
                { keySchema = definitionRef @TokenName
                , valueSchema = definitionRef @Integer
                , minItems = Nothing
                , maxItems = Nothing
                }
        , minItems = Nothing
        , maxItems = Nothing
        }

{-# INLINEABLE emptyMintValue #-}
emptyMintValue :: MintValue
emptyMintValue = UnsafeMintValue Map.empty

{-# INLINEABLE mintValueToMap #-}
mintValueToMap :: MintValue -> Map CurrencySymbol (Map TokenName Integer)
mintValueToMap (UnsafeMintValue m) = m

-- | Get the 'Value' minted by the 'MintValue'.
{-# INLINEABLE mintValueMinted #-}
mintValueMinted :: MintValue -> Value
mintValueMinted (UnsafeMintValue values) = filterQuantities (\x -> [x | x > 0]) values

{- | Get the 'Value' burned by the 'MintValue'.
All the negative quantities in the 'MintValue' become positive in the resulting 'Value'.
-}
{-# INLINEABLE mintValueBurned #-}
mintValueBurned :: MintValue -> Value
mintValueBurned (UnsafeMintValue values) = filterQuantities (\x -> [abs x | x < 0]) values

{-# INLINEABLE filterQuantities #-}
filterQuantities :: (Integer -> [Integer]) -> Map CurrencySymbol (Map TokenName Integer) -> Value
filterQuantities mapQuantity values =
  Value (Map.unsafeFromList (foldr filterTokenQuantities [] (Map.toList values)))
  where
    {-# INLINEABLE filterTokenQuantities #-}
    filterTokenQuantities
      :: (CurrencySymbol, Map TokenName Integer)
      -> [(CurrencySymbol, Map TokenName Integer)]
      -> [(CurrencySymbol, Map TokenName Integer)]
    filterTokenQuantities (currency, tokenQuantities) =
      case concatMap (traverse mapQuantity) (Map.toList tokenQuantities) of
        []         -> id
        quantities -> ((currency, Map.unsafeFromList quantities) :)

----------------------------------------------------------------------------------------------------
-- TH Splices --------------------------------------------------------------------------------------

$(makeLift ''MintValue)
