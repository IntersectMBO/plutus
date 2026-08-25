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
import Language.Haskell.TH.Syntax (Lift)
import PlutusCore.Crypto.Hash (blake2b_224)
import PlutusTx.Blueprint.Argument (ArgumentBlueprint)
import PlutusTx.Blueprint.Parameter (ParameterBlueprint)
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion (..))
import PlutusTx.Blueprint.Schema (Schema)

{-| How an applied argument is serialised into a UPLC term.

Not part of CIP-0057: the blueprint's @datum@/@redeemer@/@parameters@ schemas say
what an argument *is*, not how it reaches the program.

This type and 'ExecutionBudget' live in this module, rather than alongside the
rest of the UAL syntax in @PlutusTx.Ual.Syntax@, because they are serialised
into the blueprint and @PlutusTx.Ual.Syntax@ imports this module; putting them
there would make the two modules mutually recursive. They therefore also join
the @PlutusTx.Blueprint@ umbrella re-export. -}
data ArgumentEncoding = AsData | AsScott
  deriving stock (Show, Eq, Ord, Lift)

instance ToJSON ArgumentEncoding where
  toJSON = \case
    AsData -> "asData"
    AsScott -> "asScott"

{-| An on-chain execution budget, in Plutus cost-model units.

Deliberately not @PlutusCore.Evaluation.Machine.ExBudget.ExBudget@: that type's
fields are @SatInt@-backed newtypes tied to the evaluator's costing
representation; its JSON keys are @exBudgetCPU@ and @exBudgetMemory@ rather than
the @exCPU@ and @exMem@ this document format needs; and it has no 'Ord'. Plain
'Integer' fields keep this a document type. -}
data ExecutionBudget = MkExecutionBudget
  { budgetCPU :: Integer
  , budgetMemory :: Integer
  }
  deriving stock (Show, Eq, Ord, Lift)

instance ToJSON ExecutionBudget where
  toJSON MkExecutionBudget {..} =
    buildObject $
      requiredField "exCPU" budgetCPU
        . requiredField "exMem" budgetMemory

{-| One element of a validator's ordered applied-argument list: the terms the
compiled program is applied to, in order.

Positional and unnamed: the element carries only an encoding and a schema.

Not part of CIP-0057, which splits a validator's arguments into
@parameters@/@datum@/@redeemer@ and leaves the script context implicit; that is
not enough to apply a compiled program to concrete terms in order.

Unlike 'ArgumentEncoding' and 'ExecutionBudget' this type has no 'Lift'
instance, because 'Schema' has none. -}
data AppliedArgument (referencedTypes :: [Type]) = MkAppliedArgument
  { appliedArgumentEncoding :: ArgumentEncoding
  , appliedArgumentSchema :: Schema referencedTypes
  }
  deriving stock (Show, Eq, Ord)

instance ToJSON (AppliedArgument referencedTypes) where
  toJSON MkAppliedArgument {..} =
    buildObject $
      requiredField "encoding" appliedArgumentEncoding
        . requiredField "schema" appliedArgumentSchema

{-| A blueprint of a validator, as defined by the CIP-0057

The 'referencedTypes' phantom type parameter is used to track the types used in the contract
making sure their schemas are included in the blueprint and that they are referenced
in a type-safe way. -}
data ValidatorBlueprint (referencedTypes :: [Type]) = MkValidatorBlueprint
  { validatorTitle :: Text
  -- ^ A short and descriptive name for the validator.
  , validatorDescription :: Maybe Text
  -- ^ An informative description of the validator.
  , validatorRedeemer :: ~(ArgumentBlueprint referencedTypes)
  {-^ A description of the redeemer format expected by this validator.

  Lazy, unlike every other field here: this package's library stanza sets
  @default-extensions: Strict@, so an unannotated field would make any record
  holding a bottom redeemer bottom itself, and 'mkValidatorBlueprint' defaults
  this field to a bottom. With the annotation that bottom is only reached if the
  blueprint is used without setting the field. -}
  , validatorDatum :: Maybe (ArgumentBlueprint referencedTypes)
  -- ^ A description of the datum format expected by this validator.
  , validatorParameters :: [ParameterBlueprint referencedTypes]
  -- ^ A list of parameters required by the script.
  , validatorCompiled :: Maybe CompiledValidator
  -- ^ A full compiled and CBOR-encoded serialized flat script together with its hash.
  , validatorId :: Maybe Text
  {-^ An identifier for this validator, intended to be unique within the
  contract so that other documents can reference it. Not part of CIP-0057, and
  uniqueness is not checked here. -}
  , validatorArguments :: [AppliedArgument referencedTypes]
  {-^ The ordered list of terms the compiled program is applied to. Not part of
  CIP-0057; an empty list omits the key from the JSON. -}
  , validatorBudget :: Maybe ExecutionBudget
  {-^ The execution budget declared for this validator. Not part of CIP-0057,
  and not checked against 'validatorCompiled'. -}
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
      PlutusV4 -> 0x4

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
        . optionalField "id" validatorId
        . optionalField "arguments" (NE.nonEmpty validatorArguments)
        . optionalField "budget" validatorBudget
    where
      toHex :: ByteString -> Text
      toHex = Text.decodeUtf8 . Base16.encode

{-| A 'ValidatorBlueprint' with everything optional left out. Set the fields you
need with record-update syntax:

@
mkValidatorBlueprint
  { validatorTitle = "My Validator"
  , validatorRedeemer = ...
  }
@

Prefer this over the raw constructor: new optional fields can then be added
without breaking your call site.

'validatorRedeemer' is deliberately a bottom that names itself: CIP-0057 makes
@redeemer@ required, so there is no honest default, and a bottom is better than a
silently wrong value. It must be set. Because that field is lazy, the bottom is
not raised when the record is built but when the field is first demanded — in
practice when the blueprint is encoded. -}
mkValidatorBlueprint :: ValidatorBlueprint referencedTypes
mkValidatorBlueprint =
  MkValidatorBlueprint
    { validatorTitle = ""
    , validatorDescription = Nothing
    , validatorRedeemer =
        error "mkValidatorBlueprint: validatorRedeemer must be set"
    , validatorDatum = Nothing
    , validatorParameters = []
    , validatorCompiled = Nothing
    , validatorId = Nothing
    , validatorArguments = []
    , validatorBudget = Nothing
    }
