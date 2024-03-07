{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}

module PlutusTx.Blueprint.Contract where

import Prelude

import Control.Applicative (Alternative (empty))
import Data.Aeson (ToJSON (..), (.=))
import Data.Aeson qualified as Aeson
import Data.Aeson.Extra (optionalField, requiredField)
import Data.Aeson.Extra qualified as Aeson
import Data.Kind (Type)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Text (Text)
import PlutusTx.Blueprint.Definition (DefinitionId)
import PlutusTx.Blueprint.Preamble (Preamble)
import PlutusTx.Blueprint.Schema (Schema)
import PlutusTx.Blueprint.Validator (ValidatorBlueprint)

{- | A blueprint of a smart contract, as defined by the CIP-0057

  The 'referencedTypes' phantom type parameter is used to track the types used in the contract
  making sure their schemas are included in the blueprint and that they are referenced
  in a type-safe way.
-}
data ContractBlueprint (referencedTypes :: [Type]) = MkContractBlueprint
  { contractId          :: Maybe Text
  -- ^ An optional identifier for the contract.
  , contractPreamble    :: Preamble
  -- ^ An object with meta-information about the contract.
  , contractValidators  :: Set (ValidatorBlueprint referencedTypes)
  -- ^ A set of validator blueprints that are part of the contract.
  , contractDefinitions :: Map DefinitionId (Schema referencedTypes)
  -- ^ A registry of schema definitions used across the blueprint.
  }
  deriving stock (Show)

instance ToJSON (ContractBlueprint referencedTypes) where
  toJSON MkContractBlueprint{..} =
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
        . optionalField "definitions" (guarded (not . Map.null) contractDefinitions)
   where
    schemaUrl :: String
    schemaUrl = "https://cips.cardano.org/cips/cip57/schemas/plutus-blueprint.json"

    guarded :: (Alternative f) => (a -> Bool) -> a -> f a
    guarded p a = if p a then pure a else empty
