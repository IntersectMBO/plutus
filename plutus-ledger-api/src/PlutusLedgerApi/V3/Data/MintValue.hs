{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-unbox-small-strict-fields #-}
{-# OPTIONS_GHC -fno-unbox-strict-fields #-}

module PlutusLedgerApi.V3.Data.MintValue
  ( MintValue (..) -- Constructor is exported for testing
  , emptyMintValue
  , mintValueToMap
  , mintValueMinted
  , mintValueBurned
  )
where

import PlutusTx.Prelude

import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Data.Value (CurrencySymbol, TokenName, Value (..))
import PlutusTx.Blueprint.Class (HasBlueprintSchema (..))
import PlutusTx.Blueprint.Definition
  ( HasBlueprintDefinition (..)
  , definitionIdFromType
  , definitionRef
  )
import PlutusTx.Blueprint.Schema (MapSchema (..), Schema (..))
import PlutusTx.Blueprint.Schema.Annotation (emptySchemaInfo, title)
import PlutusTx.Data.AssocMap (Map)
import PlutusTx.Data.AssocMap qualified as Map
import PlutusTx.Lift (makeLift)
import Prettyprinter (Pretty)
import Prettyprinter.Extras (PrettyShow (PrettyShow))
import Prelude qualified as Haskell

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
  deriving stock (Generic, Haskell.Show)
  deriving newtype (ToData, FromData, UnsafeFromData)
  deriving (Pretty) via (PrettyShow MintValue)

instance Haskell.Eq MintValue where
  l == r = mintValueMinted l == mintValueMinted r && mintValueBurned l == mintValueBurned r

instance HasBlueprintDefinition MintValue where
  type Unroll MintValue = '[MintValue, CurrencySymbol, TokenName, Integer]
  definitionId = definitionIdFromType @MintValue

instance HasBlueprintSchema MintValue referencedTypes where
  schema =
    SchemaMap
      emptySchemaInfo {title = Just "MintValue"}
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
  {-# INLINEABLE schema #-}

emptyMintValue :: MintValue
emptyMintValue = UnsafeMintValue Map.empty
{-# INLINEABLE emptyMintValue #-}

mintValueToMap :: MintValue -> Map CurrencySymbol (Map TokenName Integer)
mintValueToMap (UnsafeMintValue m) = m
{-# INLINEABLE mintValueToMap #-}

-- | Get the 'Value' minted by the 'MintValue'.
mintValueMinted :: MintValue -> Value
mintValueMinted (UnsafeMintValue m) =
  mapMaybeQuantities (\x -> if x > 0 then Just x else Nothing) m
{-# INLINEABLE mintValueMinted #-}

{-| Get the 'Value' burned by the 'MintValue'.
All the negative quantities in the 'MintValue' become positive in the resulting 'Value'. -}
mintValueBurned :: MintValue -> Value
mintValueBurned (UnsafeMintValue m) =
  mapMaybeQuantities (\x -> if x < 0 then Just (abs x) else Nothing) m
{-# INLINEABLE mintValueBurned #-}

mapMaybeQuantities
  :: (Integer -> Maybe Integer)
  -> Map CurrencySymbol (Map TokenName Integer)
  -> Value
mapMaybeQuantities mapMaybeQuantity = Value . Map.mapMaybe mapMaybeCurrencies
  where
    {-# INLINEABLE mapMaybeCurrencies #-}
    mapMaybeCurrencies :: Map TokenName Integer -> Maybe (Map TokenName Integer)
    mapMaybeCurrencies map = do
      let map' = Map.mapMaybe mapMaybeQuantity map
      if Map.null map' then Nothing else Just map'
{-# INLINEABLE mapMaybeQuantities #-}

----------------------------------------------------------------------------------------------------
-- TH Splices --------------------------------------------------------------------------------------
$(makeLift ''MintValue)
