{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}

module PlutusTx.Blueprint.Argument where

import Prelude

import Data.Aeson (KeyValue ((.=)), ToJSON (..))
import Data.Aeson qualified as Aeson
import Data.Aeson.Extra
import Data.Aeson.KeyMap qualified as KeyMap
import Data.Function ((&))
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import PlutusTx.Blueprint.Purpose (Purpose)
import PlutusTx.Blueprint.Schema (Schema)

-- | Blueprint that defines a validator's runtime argument: datum or redeemer.
data ArgumentBlueprint = MkArgumentBlueprint
  { argumentTitle       :: Maybe Text
  -- ^ A short and descriptive name for the redeemer or datum.
  , argumentDescription :: Maybe Text
  -- ^ An informative description of the redeemer or datum.
  , argumentPurpose     :: Set Purpose
  -- ^ A possibly empty set of purposes for the redeemer or datum.
  , argumentSchema      :: Schema
  -- ^ A Plutus Data Schema.
  }
  deriving stock (Show, Eq)

instance ToJSON ArgumentBlueprint where
  toJSON MkArgumentBlueprint{..} =
    KeyMap.empty
      & optionalField "title" argumentTitle
      & optionalField "description" argumentDescription
      & optionalField "purpose" purpose
      & requiredField "schema" argumentSchema
      & Aeson.Object
   where
    purpose :: Maybe Aeson.Value =
      case Set.toList argumentPurpose of
        []  -> Nothing
        [x] -> Just $ toJSON x
        xs  -> Just $ Aeson.object ["oneOf" .= xs]
