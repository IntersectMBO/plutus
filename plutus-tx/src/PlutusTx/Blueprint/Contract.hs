{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}

module PlutusTx.Blueprint.Contract where

import Prelude

import Data.Aeson (ToJSON (..), (.=))
import Data.Aeson qualified as Aeson
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (catMaybes)
import Data.Set (Set)
import Data.Text (Text)
import PlutusTx.Blueprint.Definition (DefinitionId)
import PlutusTx.Blueprint.Preamble (Preamble)
import PlutusTx.Blueprint.Schema (Schema)
import PlutusTx.Blueprint.Validator (ValidatorBlueprint)

data ContractBlueprint = MkContractBlueprint
  { contractId          :: Maybe Text
  -- ^ An optional identifier for the contract
  , contractPreamble    :: Preamble
  -- ^ An object with meta-information about the contract
  , contractValidators  :: Set ValidatorBlueprint
  -- ^ An object of named validators
  , contractDefinitions :: Map DefinitionId Schema
  -- ^ A registry of definition re-used across the specification
  }
  deriving stock (Show)

instance ToJSON ContractBlueprint where
  toJSON MkContractBlueprint{..} =
    Aeson.object
      $ catMaybes
        [ Just $ "$schema" .= schemaUrl
        , fmap ("$id" .=) contractId
        , Just
            $ "$vocabulary"
            .= Aeson.object
              [ "https://json-schema.org/draft/2020-12/vocab/core" .= True
              , "https://json-schema.org/draft/2020-12/vocab/applicator" .= True
              , "https://json-schema.org/draft/2020-12/vocab/validation" .= True
              , "https://cips.cardano.org/cips/cip57" .= True
              ]
        , Just $ "preamble" .= contractPreamble
        , Just $ "validators" .= contractValidators
        , if Map.null contractDefinitions
            then Nothing
            else Just $ "definitions" .= contractDefinitions
        ]
   where
    schemaUrl :: String
    schemaUrl = "https://cips.cardano.org/cips/cip57/schemas/plutus-blueprint.json"
