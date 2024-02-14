{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}

module PlutusTx.Blueprint.Contract where

import Prelude

import Data.Aeson (ToJSON (..), (.=))
import Data.Aeson qualified as Aeson
import Data.Map (Map)
import PlutusTx.Blueprint.Definition (DefinitionId)
import PlutusTx.Blueprint.Preamble (Preamble)
import PlutusTx.Blueprint.Schema (DataSchema)
import PlutusTx.Blueprint.Validator (ValidatorBlueprint)

data ContractBlueprint = MkContractBlueprint
  { contractPreamble    :: Preamble
  -- ^ An object with meta-information about the contract
  , contractValidators  :: [ValidatorBlueprint]
  -- ^ An object of named validators
  , contractDefinitions :: Map DefinitionId DataSchema
  -- ^ A registry of definition re-used across the specification
  }
  deriving stock (Show)

instance ToJSON ContractBlueprint where
  toJSON MkContractBlueprint{..} =
    Aeson.object
      [ "preamble" .= contractPreamble
      , "validators" .= contractValidators
      , "definitions" .= contractDefinitions
      ]
