{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}

module PlutusTx.Blueprint.Parameter where

import Prelude

import Data.Aeson (ToJSON (..), (.=))
import Data.Aeson qualified as Aeson
import Data.Aeson.Extra (optionalField, requiredField)
import Data.Aeson.KeyMap qualified as KeyMap
import Data.Function ((&))
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import PlutusTx.Blueprint.Purpose (Purpose)
import PlutusTx.Blueprint.Schema (Schema)

-- | Blueprint that defines validator's compile-time parameter.
data ParameterBlueprint = MkParameterBlueprint
  { parameterTitle       :: Maybe Text
  -- ^ A short and descriptive name for the parameter.
  , parameterDescription :: Maybe Text
  -- ^ An informative description of the parameter.
  , parameterPurpose     :: Set Purpose
  -- ^ One of "spend", "mint", "withdraw" or "publish", or a oneOf applicator of those.
  , parameterSchema      :: Schema
  -- ^ A Plutus Data Schema.
  }
  deriving stock (Show, Eq)

instance ToJSON ParameterBlueprint where
  toJSON MkParameterBlueprint{..} =
    KeyMap.empty
      & optionalField "title" parameterTitle
      & optionalField "description" parameterDescription
      & optionalField "purpose" purpose
      & requiredField "schema" parameterSchema
      & Aeson.Object
   where
    purpose :: Maybe Aeson.Value =
      case Set.toList parameterPurpose of
        []  -> Nothing
        [x] -> Just $ toJSON x
        xs  -> Just $ Aeson.object ["oneOf" .= xs]
