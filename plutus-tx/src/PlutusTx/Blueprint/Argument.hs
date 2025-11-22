{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module PlutusTx.Blueprint.Argument where

import Prelude

import Data.Aeson (ToJSON (..))
import Data.Aeson.Extra (buildObject, optionalField, requiredField)
import Data.Kind (Type)
import Data.Set (Set)
import Data.Text (Text)
import PlutusTx.Blueprint.Parameter (oneOfASet)
import PlutusTx.Blueprint.Purpose (Purpose)
import PlutusTx.Blueprint.Schema (Schema)

-- | Blueprint that defines a validator's runtime argument: datum or redeemer.
data ArgumentBlueprint (referencedTypes :: [Type]) = MkArgumentBlueprint
  { argumentTitle :: Maybe Text
  -- ^ A short and descriptive name for the redeemer or datum.
  , argumentDescription :: Maybe Text
  -- ^ An informative description of the redeemer or datum.
  , argumentPurpose :: Set Purpose
  -- ^ A possibly empty set of purposes for the redeemer or datum.
  , argumentSchema :: Schema referencedTypes
  -- ^ A Plutus Data Schema.
  }
  deriving stock (Show, Eq, Ord)

instance ToJSON (ArgumentBlueprint referencedTypes) where
  toJSON MkArgumentBlueprint {..} =
    buildObject $
      requiredField "schema" argumentSchema
        . optionalField "title" argumentTitle
        . optionalField "description" argumentDescription
        . optionalField "purpose" (oneOfASet argumentPurpose)
