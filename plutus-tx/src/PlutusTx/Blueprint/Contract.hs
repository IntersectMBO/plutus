{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module PlutusTx.Blueprint.Contract where

import Prelude

import Data.Aeson (ToJSON (..), (.=))
import Data.Aeson qualified as Aeson
import Data.Aeson.Extra (optionalField, requiredField)
import Data.Aeson.Extra qualified as Aeson
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Text (Text)
import PlutusPrelude (ensure)
import PlutusTx.Blueprint.Definition (DefinitionId, Definitions, definitionsToMap)
import PlutusTx.Blueprint.Preamble (Preamble)
import PlutusTx.Blueprint.Validator (ValidatorBlueprint)

{-| A blueprint of a smart contract, as defined by the CIP-0057

The 'referencedTypes' type variable is used to track the types used in the contract
making sure their schemas are included in the blueprint and that they are referenced
in a type-safe way. See Note ["Unrolling" types] for more details. -}
data ContractBlueprint where
  MkContractBlueprint
    :: forall referencedTypes
     . { contractId :: Maybe Text
       -- ^ An optional identifier for the contract.
       , contractPreamble :: Preamble
       -- ^ An object with meta-information about the contract.
       , contractValidators :: Set (ValidatorBlueprint referencedTypes)
       -- ^ A set of validator blueprints that are part of the contract.
       , contractDefinitions :: Definitions referencedTypes
       -- ^ A registry of schema definitions used across the blueprint.
       }
    -> ContractBlueprint

instance ToJSON ContractBlueprint where
  toJSON MkContractBlueprint {..} =
    Aeson.buildObject $
      requiredField "$schema" schemaUrl
        . requiredField
          "$vocabulary"
          ( Aeson.object
              [ "https://json-schema.org/draft/2020-12/vocab/core" .= True
              , "https://json-schema.org/draft/2020-12/vocab/applicator" .= True
              , "https://json-schema.org/draft/2020-12/vocab/validation" .= True
              , "https://cips.cardano.org/cips/cip57" .= True
              ]
          )
        . requiredField "preamble" contractPreamble
        . requiredField "validators" contractValidators
        . optionalField "$id" contractId
        . optionalField "definitions" definitions
    where
      schemaUrl :: String
      schemaUrl = "https://cips.cardano.org/cips/cip57/schemas/plutus-blueprint.json"

      definitions :: Maybe (Map DefinitionId Aeson.Value)
      definitions = ensure (not . Map.null) (definitionsToMap contractDefinitions toJSON)
