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

module PlutusLedgerApi.V3.MintValue
  ( MintValue (..) -- Constructor is exported for testing
  , emptyMintValue
  , mintValueToMap
  , mintValueMinted
  , mintValueBurned
  )
where

import PlutusTx.Prelude as PlutusTx

import Control.DeepSeq (NFData)
import Data.Data (Data)
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Value (CurrencySymbol, TokenName, Value (..))
import PlutusTx.AssocMap (Map)
import PlutusTx.AssocMap qualified as Map
import PlutusTx.Blueprint.Class (HasBlueprintSchema (..))
import PlutusTx.Blueprint.Definition
  ( HasBlueprintDefinition (..)
  , definitionIdFromType
  , definitionRef
  )
import PlutusTx.Blueprint.Schema (MapSchema (..), Schema (..))
import PlutusTx.Blueprint.Schema.Annotation (emptySchemaInfo, title)
import PlutusTx.Lift (makeLift)
import PlutusTx.List qualified as List
import PlutusTx.Traversable qualified as T
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
newtype MintValue = UnsafeMintValue {unMintValue :: Map CurrencySymbol (Map TokenName Integer)}
  deriving stock (Generic, Data, Haskell.Show)
  deriving anyclass (NFData)
  deriving newtype (ToData, FromData, UnsafeFromData)
  deriving (Pretty) via (PrettyShow MintValue)

-- Manual Eq instance: two MintValues are equal if they mint and burn the same assets,
-- regardless of internal Map representation. Cannot use deriveEq for semantic equality.
instance PlutusTx.Eq MintValue where
  {-# INLINEABLE (==) #-}
  l == r = mintValueMinted l == mintValueMinted r && mintValueBurned l == mintValueBurned r

instance Haskell.Eq MintValue where
  (==) = (PlutusTx.==)

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
mintValueMinted (UnsafeMintValue values) = filterQuantities (\x -> [x | x > 0]) values
{-# INLINEABLE mintValueMinted #-}

{-| Get the 'Value' burned by the 'MintValue'.
All the negative quantities in the 'MintValue' become positive in the resulting 'Value'. -}
mintValueBurned :: MintValue -> Value
mintValueBurned (UnsafeMintValue values) = filterQuantities (\x -> [abs x | x < 0]) values
{-# INLINEABLE mintValueBurned #-}

filterQuantities :: (Integer -> [Integer]) -> Map CurrencySymbol (Map TokenName Integer) -> Value
filterQuantities mapQuantity values =
  Value (Map.unsafeFromList (List.foldr filterTokenQuantities [] (Map.toList values)))
  where
    {-# INLINEABLE filterTokenQuantities #-}
    filterTokenQuantities
      :: (CurrencySymbol, Map TokenName Integer)
      -> [(CurrencySymbol, Map TokenName Integer)]
      -> [(CurrencySymbol, Map TokenName Integer)]
    filterTokenQuantities (currency, tokenQuantities) =
      case List.concatMap (T.traverse mapQuantity) (Map.toList tokenQuantities) of
        [] -> id
        quantities -> ((currency, Map.unsafeFromList quantities) :)
{-# INLINEABLE filterQuantities #-}

----------------------------------------------------------------------------------------------------
-- TH Splices --------------------------------------------------------------------------------------

$(makeLift ''MintValue)
