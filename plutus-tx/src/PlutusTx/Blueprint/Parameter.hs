{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}

module PlutusTx.Blueprint.Parameter where

import Prelude

import Data.Aeson (ToJSON (..), (.=))
import Data.Aeson qualified as Aeson
import Data.Maybe (catMaybes)
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
  deriving stock (Show)

instance ToJSON ParameterBlueprint where
  toJSON MkParameterBlueprint{..} =
    Aeson.object
      $ catMaybes
        [ fmap ("title" .=) parameterTitle
        , fmap ("description" .=) parameterDescription
        , case Set.size parameterPurpose of
            0 -> Nothing
            1 -> Just $ "purpose" .= Set.elemAt 0 parameterPurpose -- safe usage
            _ -> Just $ "purpose" .= Aeson.object ["oneOf" .= parameterPurpose]
        , Just $ "schema" .= parameterSchema
        ]
