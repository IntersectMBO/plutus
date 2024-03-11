{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}

module PlutusTx.Blueprint.Contract where

import Prelude

import Data.Aeson (ToJSON (..), (.=))
import Data.Aeson qualified as Aeson
import Data.Aeson.Extra (optionalField, requiredField)
import Data.Aeson.Extra qualified as Aeson
import Data.Kind (Type)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Text (Text)
import PlutusPrelude (ensure)
import PlutusTx.Blueprint.Definition (DefinitionId, UnrollAll)
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

{- Note ["Unrolling" types]

ContractBlueprint needs to be parameterized by a list of types used in
a contract's type signature (including nested types) in order to:
  a) produce a JSON-schema definition for every type used.
  b) ensure that the schema definitions are referenced in a type-safe way.

Given the following contract validator's type signature:

  typedValidator :: Redeemer -> Datum -> ScriptContext -> Bool

and the following data type definitions:

  data Redeemer = MkRedeemer MyStruct
  data MyStruct = MkMyStruct { field1 :: Integer, field2 :: Bool }
  type Datum = ()

The ContractBlueprint type should be:

  ContractBlueprint '[Redeemer, MyStruct, Integer, Bool, ()]

However, for contract blurprints authors specifying all the nested types manually is
cumbersome and error-prone. To make it easier to work with, we provide the Unroll type family
that can be used to traverse a type accumulating all types nested within it:

  Unroll Redeemer ~ '[Redeemer, MyStruct, Integer, Bool]
  UnrollAll '[Redeemer, Datum] ~ '[Redeemer, MyStruct, Integer, Bool, ()]

This way blueprint authors can specify the top-level types used in a contract and the UnrollAll
type family will take care of discovering all the nested types:

  Blueprint '[Redeemer, Datum]

  is equivalent to

  ContractBlueprint '[Redeemer, MyStruct, Integer, Bool, ()]

-}

-- | A contract blueprint with all (nested) types discovered from a list of top-level types.
type Blueprint topTypes = ContractBlueprint (UnrollAll topTypes)

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
        . optionalField "definitions" (ensure (not . Map.null) contractDefinitions)
   where
    schemaUrl :: String
    schemaUrl = "https://cips.cardano.org/cips/cip57/schemas/plutus-blueprint.json"
