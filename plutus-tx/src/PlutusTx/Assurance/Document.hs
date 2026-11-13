{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

{-| Types for the assurance document defined by the Plutus Blueprint Assurance
Documents CIP: a standalone JSON document publishing behavioural claims about the
validators of a CIP-0057 blueprint.

Two fields are extensions this producer needs and the CIP adds:
'assuranceFormalFragments' (named, importable blocks of formal definitions) and
'formalUses' (which fragments a statement elaborates against). The CIP's
meta-schema sets no @additionalProperties: false@, so a document carrying them
validates against the published schema as-is.

These types do not enforce the CIP's cardinality constraints. Several arrays
that the meta-schema marks @required@ also carry @minItems: 1@, so they can
neither be omitted nor be empty; the fields are plain lists here and it is the
caller's job to populate them. The individual fields say which. -}
module PlutusTx.Assurance.Document where

import Prelude

import Data.Aeson (ToJSON (..))
import Data.Aeson qualified as Aeson
import Data.Aeson.Extra (buildObject, optionalField, requiredField)
import Data.Aeson.Key qualified as Key
import Data.Aeson.KeyMap qualified as KeyMap
import Data.List.NonEmpty qualified as NE
import Data.Text (Text)

-- | The @$schema@ value the CIP's meta-schema pins with @const@.
schemaUri :: Text
schemaUri = "https://cips.cardano.org/cips/cipXXXX/schemas/assurance.json"

data AssuranceDocument = MkAssuranceDocument
  { assurancePreamble :: AssurancePreamble
  , assuranceBlueprint :: BlueprintRef
  , assuranceLanguages :: [(Text, RegistryEntry)]
  {-^ Keyed registry of annotation languages. Omitted when empty. Keys must
  match @^[A-Za-z0-9_-]+$@; not checked here. -}
  , assuranceTools :: [(Text, RegistryEntry)]
  {-^ Keyed registry of tools. Omitted when empty. Keys must match
  @^[A-Za-z0-9_-]+$@; not checked here. -}
  , assuranceFormalFragments :: [FormalFragment]
  -- ^ CIP extension. Omitted when empty.
  , assuranceProperties :: [Property]
  {-^ Required and @minItems: 1@, so an empty list emits @[]@ and yields a
  document the CIP's schema rejects. Not enforced here. -}
  }
  deriving stock (Eq, Show)

instance ToJSON AssuranceDocument where
  toJSON MkAssuranceDocument {..} =
    buildObject $
      requiredField "$schema" schemaUri
        . requiredField "preamble" assurancePreamble
        . requiredField "blueprint" assuranceBlueprint
        . optionalField "languages" (registry assuranceLanguages)
        . optionalField "tools" (registry assuranceTools)
        . optionalField "formalFragments" (NE.nonEmpty assuranceFormalFragments)
        . requiredField "properties" assuranceProperties
    where
      registry [] = Nothing
      registry kvs =
        Just . Aeson.Object . KeyMap.fromList $
          [(Key.fromText k, toJSON v) | (k, v) <- kvs]

data AssurancePreamble = MkAssurancePreamble
  { assuranceTitle :: Text
  , assuranceDescription :: Maybe Text
  , assuranceVersion :: Maybe Text
  , assuranceAuthors :: [Text]
  {-^ Required and @minItems: 1@, so an empty list emits @[]@ and yields a
  document the CIP's schema rejects. Not enforced here. -}
  , assuranceCreated :: Text
  -- ^ @YYYY-MM-DD@. The CIP's schema enforces the shape.
  , assuranceLicense :: Maybe Text
  }
  deriving stock (Eq, Show)

instance ToJSON AssurancePreamble where
  toJSON MkAssurancePreamble {..} =
    buildObject $
      requiredField "title" assuranceTitle
        . requiredField "authors" assuranceAuthors
        . requiredField "created" assuranceCreated
        . optionalField "description" assuranceDescription
        . optionalField "version" assuranceVersion
        . optionalField "license" assuranceLicense

data BlueprintRef = MkBlueprintRef
  { blueprintUri :: Text
  , blueprintHash :: Maybe Digest
  }
  deriving stock (Eq, Show)

instance ToJSON BlueprintRef where
  toJSON MkBlueprintRef {..} =
    buildObject $
      requiredField "uri" blueprintUri
        . optionalField "hash" blueprintHash

data Digest = MkDigest
  { digestAlg :: Text
  , digestValue :: Text
  -- ^ Lowercase hex.
  }
  deriving stock (Eq, Show)

instance ToJSON Digest where
  toJSON MkDigest {..} =
    buildObject $
      requiredField "alg" digestAlg
        . requiredField "digest" digestValue

data RegistryEntry = MkRegistryEntry
  { registryName :: Text
  , registryVersion :: Text
  , registryUri :: Maybe Text
  , registryDescription :: Maybe Text
  }
  deriving stock (Eq, Show)

instance ToJSON RegistryEntry where
  toJSON MkRegistryEntry {..} =
    buildObject $
      requiredField "name" registryName
        . requiredField "version" registryVersion
        . optionalField "uri" registryUri
        . optionalField "description" registryDescription

{-| A named block of formal definitions. The id is the surface module name, and
'fragmentImports' mirror that module's imports restricted to modules that also
produced a fragment. -}
data FormalFragment = MkFormalFragment
  { fragmentId :: Text
  , fragmentLanguage :: Text
  , fragmentImports :: [Text]
  -- ^ Omitted when empty.
  , fragmentSource :: Text
  }
  deriving stock (Eq, Show)

instance ToJSON FormalFragment where
  toJSON MkFormalFragment {..} =
    buildObject $
      requiredField "id" fragmentId
        . requiredField "language" fragmentLanguage
        . optionalField "imports" (NE.nonEmpty fragmentImports)
        . requiredField "source" fragmentSource

data Property = MkProperty
  { propertyIdent :: Text
  -- ^ Must match @^[A-Za-z0-9_-]+$@; not checked here.
  , propertyTitle :: Maybe Text
  , propertyValidators :: [Text]
  {-^ @scope.validators@: required and @minItems: 1@, so an empty list emits
  @[]@ and yields a document the CIP's schema rejects. Not enforced here. -}
  , propertyStatement :: Statement
  }
  deriving stock (Eq, Show)

instance ToJSON Property where
  toJSON MkProperty {..} =
    buildObject $
      requiredField "id" propertyIdent
        . requiredField "scope" (Aeson.object ["validators" Aeson..= propertyValidators])
        . requiredField "statement" propertyStatement
        . optionalField "title" propertyTitle

data Statement = MkStatement
  { statementText :: Text
  -- ^ @minLength: 1@; not checked here.
  , statementFormal :: Maybe FormalStatement
  }
  deriving stock (Eq, Show)

instance ToJSON Statement where
  toJSON MkStatement {..} =
    buildObject $
      requiredField "text" statementText
        . optionalField "formal" statementFormal

data FormalStatement = MkFormalStatement
  { formalLanguage :: Text
  , formalUses :: [Text]
  -- ^ CIP extension. Omitted when empty.
  , formalSource :: Text
  }
  deriving stock (Eq, Show)

instance ToJSON FormalStatement where
  toJSON MkFormalStatement {..} =
    buildObject $
      requiredField "language" formalLanguage
        . requiredField "source" formalSource
        . optionalField "uses" (NE.nonEmpty formalUses)
