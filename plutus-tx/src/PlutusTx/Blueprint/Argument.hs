{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}

module PlutusTx.Blueprint.Argument where

import Prelude

import Data.Aeson (ToJSON (..), (.=))
import Data.Aeson qualified as Aeson
import Data.Maybe (catMaybes)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import PlutusTx.Blueprint.Purpose (Purpose)
import PlutusTx.Blueprint.Schema (DataSchema (..))

data ArgumentBlueprint = MkArgumentBlueprint
  { argumentTitle       :: Maybe Text
  -- ^ A short and descriptive name for the redeemer or datum.
  , argumentDescription :: Maybe Text
  -- ^ An informative description of the redeemer or datum.
  , argumentPurpose     :: Set Purpose
  -- ^ A possibly empty set of purposes for the redeemer or datum.
  , argumentSchema      :: DataSchema
  -- ^ A Plutus Data Schema using the core vocabulary defined below,
  -- or a oneOf applicator of Plutus Data Schemas
  }
  deriving stock (Show)

instance ToJSON ArgumentBlueprint where
  toJSON MkArgumentBlueprint{..} =
    Aeson.object
      $ catMaybes
        [ fmap ("title" .=) argumentTitle
        , fmap ("description" .=) argumentDescription
        , case Set.size argumentPurpose of
            0 -> Nothing
            1 -> Just $ "purpose" .= Set.elemAt 0 argumentPurpose -- safe usage
            _ -> Just $ "purpose" .= Aeson.object ["oneOf" .= argumentPurpose]
        , Just $ "schema" .= argumentSchema
        ]
