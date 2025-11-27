{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module PlutusTx.Blueprint.Validator where

import Prelude

import Data.Aeson (ToJSON (..))
import Data.Aeson.Extra (buildObject, optionalField, requiredField)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as Base16
import Data.Kind (Type)
import Data.List.NonEmpty qualified as NE
import Data.Text (Text)
import Data.Text.Encoding qualified as Text
import PlutusCore.Crypto.Hash (blake2b_224)
import PlutusTx.Blueprint.Argument (ArgumentBlueprint)
import PlutusTx.Blueprint.Parameter (ParameterBlueprint)
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion (..))

{-| A blueprint of a validator, as defined by the CIP-0057

The 'referencedTypes' phantom type parameter is used to track the types used in the contract
making sure their schemas are included in the blueprint and that they are referenced
in a type-safe way. -}
data ValidatorBlueprint (referencedTypes :: [Type]) = MkValidatorBlueprint
  { validatorTitle :: Text
  -- ^ A short and descriptive name for the validator.
  , validatorDescription :: Maybe Text
  -- ^ An informative description of the validator.
  , validatorRedeemer :: ArgumentBlueprint referencedTypes
  -- ^ A description of the redeemer format expected by this validator.
  , validatorDatum :: Maybe (ArgumentBlueprint referencedTypes)
  -- ^ A description of the datum format expected by this validator.
  , validatorParameters :: [ParameterBlueprint referencedTypes]
  -- ^ A list of parameters required by the script.
  , validatorCompiled :: Maybe CompiledValidator
  -- ^ A full compiled and CBOR-encoded serialized flat script together with its hash.
  }
  deriving stock (Show, Eq, Ord)

data CompiledValidator = MkCompiledValidator
  { compiledValidatorCode :: ByteString
  , compiledValidatorHash :: ByteString
  }
  deriving stock (Show, Eq, Ord)

compiledValidator :: PlutusVersion -> ByteString -> CompiledValidator
compiledValidator version code =
  MkCompiledValidator
    { compiledValidatorCode = code
    , compiledValidatorHash =
        blake2b_224 (BS.singleton (versionTag version) <> code)
    }
  where
    versionTag = \case
      PlutusV1 -> 0x1
      PlutusV2 -> 0x2
      PlutusV3 -> 0x3

instance ToJSON (ValidatorBlueprint referencedTypes) where
  toJSON MkValidatorBlueprint {..} =
    buildObject $
      requiredField "title" validatorTitle
        . requiredField "redeemer" validatorRedeemer
        . optionalField "description" validatorDescription
        . optionalField "datum" validatorDatum
        . optionalField "parameters" (NE.nonEmpty validatorParameters)
        . optionalField "compiledCode" (toHex . compiledValidatorCode <$> validatorCompiled)
        . optionalField "hash" (toHex . compiledValidatorHash <$> validatorCompiled)
    where
      toHex :: ByteString -> Text
      toHex = Text.decodeUtf8 . Base16.encode
