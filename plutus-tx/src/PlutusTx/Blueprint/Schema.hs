{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module PlutusTx.Blueprint.Schema where

import Control.Lens.Plated (Plated)
import Data.Aeson (ToJSON (..), (.=))
import Data.Aeson qualified as Aeson
import Data.Aeson.Extra (optionalField, requiredField)
import Data.Aeson.KeyMap qualified as KeyMap
import Data.ByteString (ByteString)
import Data.ByteString.Base16 qualified as Base16
import Data.Data (Data, Typeable)
import Data.Function ((&))
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty, nonEmpty)
import Data.Text (Text)
import Data.Text.Encoding qualified as Text
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import PlutusTx.Blueprint.Definition.Id (DefinitionId, definitionIdToText)
import PlutusTx.Blueprint.Schema.Annotation (SchemaInfo, comment, description, title)
import Prelude hiding (max, maximum, min, minimum)

{-| Blueprint schema definition, as defined by the CIP-0057:
  https://github.com/cardano-foundation/CIPs/tree/master/CIP-0057#core-vocabulary

  The 'referencedTypes' phantom type parameter is used to track the types used in the contract
  making sure their schemas are included in the blueprint and that they are referenced
  in a type-safe way. -}
data Schema (referencedTypes :: [Type])
  = SchemaInteger SchemaInfo IntegerSchema
  | SchemaBytes SchemaInfo BytesSchema
  | SchemaList SchemaInfo (ListSchema referencedTypes)
  | SchemaMap SchemaInfo (MapSchema referencedTypes)
  | SchemaConstructor SchemaInfo (ConstructorSchema referencedTypes)
  | SchemaBuiltInData SchemaInfo
  | SchemaBuiltInUnit SchemaInfo
  | SchemaBuiltInBoolean SchemaInfo
  | SchemaBuiltInInteger SchemaInfo
  | SchemaBuiltInBytes SchemaInfo
  | SchemaBuiltInString SchemaInfo
  | SchemaBuiltInPair SchemaInfo (PairSchema referencedTypes)
  | SchemaBuiltInList SchemaInfo (Schema referencedTypes)
  | SchemaOneOf (NonEmpty (Schema referencedTypes))
  | SchemaAnyOf (NonEmpty (Schema referencedTypes))
  | SchemaAllOf (NonEmpty (Schema referencedTypes))
  | SchemaNot (Schema referencedTypes)
  | SchemaDefinitionRef DefinitionId
  deriving stock (Eq, Ord, Show, Generic, Data)

deriving anyclass instance Typeable referencedTypes => Plated (Schema referencedTypes)

instance ToJSON (Schema referencedTypes) where
  toJSON = \case
    SchemaInteger info MkIntegerSchema {..} ->
      dataType info "integer"
        & optionalField "multipleOf" multipleOf
        & optionalField "minimum" minimum
        & optionalField "maximum" maximum
        & optionalField "exclusiveMinimum" exclusiveMinimum
        & optionalField "exclusiveMaximum" exclusiveMaximum
        & Aeson.Object
    SchemaBytes info MkBytesSchema {..} ->
      dataType info "bytes"
        & optionalField "enum" (fmap toHex <$> nonEmpty enum)
        & optionalField "maxLength" maxLength
        & optionalField "minLength" minLength
        & Aeson.Object
      where
        toHex :: ByteString -> Text
        toHex = Text.decodeUtf8 . Base16.encode
    SchemaList info MkListSchema {..} ->
      dataType info "list"
        & requiredField "items" itemSchema
        & optionalField "minItems" minItems
        & optionalField "maxItems" maxItems
        & optionalField "uniqueItems" uniqueItems
        & Aeson.Object
    SchemaMap info MkMapSchema {..} ->
      dataType info "map"
        & requiredField "keys" keySchema
        & requiredField "values" valueSchema
        & optionalField "minItems" minItems
        & optionalField "maxItems" maxItems
        & Aeson.Object
    SchemaConstructor info MkConstructorSchema {..} ->
      dataType info "constructor"
        & requiredField "index" index
        & requiredField "fields" fieldSchemas
        & Aeson.Object
    SchemaBuiltInData info ->
      Aeson.Object $ infoFields info
    SchemaBuiltInUnit info ->
      Aeson.Object $ dataType info "#unit"
    SchemaBuiltInBoolean info ->
      Aeson.Object $ dataType info "#boolean"
    SchemaBuiltInInteger info ->
      Aeson.Object $ dataType info "#integer"
    SchemaBuiltInBytes info ->
      Aeson.Object $ dataType info "#bytes"
    SchemaBuiltInString info ->
      Aeson.Object $ dataType info "#string"
    SchemaBuiltInPair info MkPairSchema {left, right} ->
      dataType info "#pair"
        & requiredField "left" left
        & requiredField "right" right
        & Aeson.Object
    SchemaBuiltInList info schema ->
      dataType info "#list"
        & requiredField "items" schema
        & Aeson.Object
    SchemaOneOf schemas ->
      Aeson.object ["oneOf" .= schemas]
    SchemaAnyOf schemas ->
      Aeson.object ["anyOf" .= schemas]
    SchemaAllOf schemas ->
      Aeson.object ["allOf" .= schemas]
    SchemaNot schema ->
      Aeson.object ["not" .= schema]
    SchemaDefinitionRef definitionId ->
      Aeson.object ["$ref" .= ("#/definitions/" <> definitionIdToText definitionId)]
    where
      dataType :: SchemaInfo -> String -> Aeson.Object
      dataType info ty = requiredField "dataType" ty (infoFields info)

      infoFields :: SchemaInfo -> Aeson.Object
      infoFields info =
        KeyMap.empty
          & optionalField "title" (title info)
          & optionalField "description" (description info)
          & optionalField "$comment" (comment info)

withSchemaInfo :: (SchemaInfo -> SchemaInfo) -> Schema referencedTypes -> Schema referencedTypes
withSchemaInfo f = \case
  SchemaInteger info schema -> SchemaInteger (f info) schema
  SchemaBytes info schema -> SchemaBytes (f info) schema
  SchemaList info schema -> SchemaList (f info) schema
  SchemaMap info schema -> SchemaMap (f info) schema
  SchemaConstructor info schema -> SchemaConstructor (f info) schema
  SchemaBuiltInData info -> SchemaBuiltInData (f info)
  SchemaBuiltInUnit info -> SchemaBuiltInUnit (f info)
  SchemaBuiltInBoolean info -> SchemaBuiltInBoolean (f info)
  SchemaBuiltInInteger info -> SchemaBuiltInInteger (f info)
  SchemaBuiltInBytes info -> SchemaBuiltInBytes (f info)
  SchemaBuiltInString info -> SchemaBuiltInString (f info)
  SchemaBuiltInPair info schema -> SchemaBuiltInPair (f info) schema
  SchemaBuiltInList info schema -> SchemaBuiltInList (f info) schema
  SchemaOneOf schemas -> SchemaOneOf schemas
  SchemaAnyOf schemas -> SchemaAnyOf schemas
  SchemaAllOf schemas -> SchemaAllOf schemas
  SchemaNot schema -> SchemaNot schema
  SchemaDefinitionRef definitionId -> SchemaDefinitionRef definitionId

data IntegerSchema = MkIntegerSchema
  { multipleOf :: Maybe Integer
  -- ^ An instance is valid if division by this value results in an integer.
  , minimum :: Maybe Integer
  -- ^ An instance is valid only if it is greater than or exactly equal to "minimum".
  , maximum :: Maybe Integer
  -- ^ An instance is valid only if it is less than or exactly equal to "maximum".
  , exclusiveMinimum :: Maybe Integer
  -- ^ An instance is valid only if it is strictly greater than "exclusiveMinimum".
  , exclusiveMaximum :: Maybe Integer
  -- ^ An instance is valid only if it is strictly less than "exclusiveMaximum".
  }
  deriving stock (Eq, Ord, Show, Generic, Data)

emptyIntegerSchema :: IntegerSchema
emptyIntegerSchema =
  MkIntegerSchema
    { multipleOf = Nothing
    , minimum = Nothing
    , maximum = Nothing
    , exclusiveMinimum = Nothing
    , exclusiveMaximum = Nothing
    }

data BytesSchema = MkBytesSchema
  { enum :: [ByteString]
  {-^ An instance validates successfully if once hex-encoded,
  its value matches one of the specified values. -}
  , minLength :: Maybe Natural
  -- ^ An instance is valid if its length is greater than, or equal to, this value.
  , maxLength :: Maybe Natural
  -- ^ An instance is valid if its length is less than, or equal to, this value.
  }
  deriving stock (Eq, Ord, Show, Generic, Data)

emptyBytesSchema :: BytesSchema
emptyBytesSchema = MkBytesSchema {enum = [], minLength = Nothing, maxLength = Nothing}

data ListSchema (referencedTypes :: [Type]) = MkListSchema
  { itemSchema :: Schema referencedTypes
  -- ^ Element schema
  , minItems :: Maybe Natural
  -- ^ An array instance is valid if its size is greater than, or equal to, this value.
  , maxItems :: Maybe Natural
  -- ^ An array instance is valid if its size is less than, or equal to, this value.
  , uniqueItems :: Maybe Bool
  {-^ If this value is false, the instance validates successfully.
  If it is set to True, the instance validates successfully if all of its elements are unique. -}
  }
  deriving stock (Eq, Ord, Show, Generic, Data)

mkListSchema :: Schema referencedTypes -> ListSchema referencedTypes
mkListSchema itemSchema =
  MkListSchema
    { itemSchema
    , minItems = Nothing
    , maxItems = Nothing
    , uniqueItems = Nothing
    }

data MapSchema (referencedTypes :: [Type]) = MkMapSchema
  { keySchema :: Schema referencedTypes
  -- ^ Key schema
  , valueSchema :: Schema referencedTypes
  -- ^ Value schema
  , minItems :: Maybe Natural
  -- ^ A map instance is valid if its size is greater than, or equal to, this value.
  , maxItems :: Maybe Natural
  -- ^ A map instance is valid if its size is less than, or equal to, this value.
  }
  deriving stock (Eq, Ord, Show, Generic, Data)

data ConstructorSchema (referencedTypes :: [Type]) = MkConstructorSchema
  { index :: Natural
  -- ^ Constructor index
  , fieldSchemas :: [Schema referencedTypes]
  -- ^ Field schemas
  }
  deriving stock (Eq, Ord, Show, Generic, Data)

data PairSchema (referencedTypes :: [Type]) = MkPairSchema
  { left :: Schema referencedTypes
  -- ^ Schema of the first element
  , right :: Schema referencedTypes
  -- ^ Schema of the second element
  }
  deriving stock (Eq, Ord, Show, Generic, Data)
