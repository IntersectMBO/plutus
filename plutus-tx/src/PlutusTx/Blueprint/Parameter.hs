{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module PlutusTx.Blueprint.Parameter where

import Prelude

import Data.Aeson (ToJSON (..), (.=))
import Data.Aeson qualified as Aeson
import Data.Aeson.Extra (buildObject, optionalField, requiredField)
import Data.Kind (Type)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import PlutusTx.Blueprint.Purpose (Purpose)
import PlutusTx.Blueprint.Schema (Schema)

{-| Blueprint that defines validator's compile-time parameter.

  The 'referencedTypes' phantom type parameter is used to track the types used in the contract
  making sure their schemas are included in the blueprint and that they are referenced
  in a type-safe way. -}
data ParameterBlueprint (referencedTypes :: [Type]) = MkParameterBlueprint
  { parameterTitle :: Maybe Text
  -- ^ A short and descriptive name for the parameter.
  , parameterDescription :: Maybe Text
  -- ^ An informative description of the parameter.
  , parameterPurpose :: Set Purpose
  -- ^ One of "spend", "mint", "withdraw" or "publish", or a oneOf applicator of those.
  , parameterSchema :: Schema referencedTypes
  -- ^ A Plutus Data Schema.
  }
  deriving stock (Show, Eq, Ord)

instance ToJSON (ParameterBlueprint referencedTypes) where
  toJSON MkParameterBlueprint {..} =
    buildObject $
      requiredField "schema" parameterSchema
        . optionalField "title" parameterTitle
        . optionalField "description" parameterDescription
        . optionalField "purpose" (oneOfASet parameterPurpose)

----------------------------------------------------------------------------------------------------
-- Helper functions --------------------------------------------------------------------------------

oneOfASet :: ToJSON a => Set a -> Maybe Aeson.Value
oneOfASet s =
  case Set.toList s of
    [] -> Nothing
    [x] -> Just $ toJSON x
    xs -> Just $ Aeson.object ["oneOf" .= xs]
