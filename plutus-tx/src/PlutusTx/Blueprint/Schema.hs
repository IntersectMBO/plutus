{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusTx.Blueprint.Schema where

import Control.Lens.Plated (Plated)
import Data.Aeson (ToJSON (..), (.=))
import Data.Aeson qualified as Aeson
import Data.Aeson.Extra (optionalField, requiredField)
import Data.Aeson.KeyMap qualified as KeyMap
import Data.ByteString (ByteString)
import Data.ByteString.Base16 qualified as Base16
import Data.Data (Data)
import Data.Function ((&))
import Data.List.NonEmpty (NonEmpty, nonEmpty)
import Data.Text (Text)
import Data.Text.Encoding qualified as Text
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import PlutusTx.Blueprint.Definition.Id (DefinitionId, definitionIdToText)
import Prelude hiding (max, maximum, min, minimum)

{- | Blueprint schema definition, as defined by the CIP-0057:
https://github.com/cardano-foundation/CIPs/tree/master/CIP-0057#core-vocabulary
-}
data Schema
  = SchemaInteger SchemaInfo IntegerSchema
  | SchemaBytes SchemaInfo BytesSchema
  | SchemaList SchemaInfo ListSchema
  | SchemaMap SchemaInfo MapSchema
  | SchemaConstructor SchemaInfo ConstructorSchema
  | SchemaBuiltInData SchemaInfo
  | SchemaBuiltInUnit SchemaInfo
  | SchemaBuiltInBoolean SchemaInfo
  | SchemaBuiltInInteger SchemaInfo
  | SchemaBuiltInBytes SchemaInfo
  | SchemaBuiltInString SchemaInfo
  | SchemaBuiltInPair SchemaInfo PairSchema
  | SchemaBuiltInList SchemaInfo Schema
  | SchemaOneOf (NonEmpty Schema)
  | SchemaAnyOf (NonEmpty Schema)
  | SchemaAllOf (NonEmpty Schema)
  | SchemaNot Schema
  | SchemaDefinitionRef DefinitionId
  deriving stock (Eq, Show, Generic, Data)

deriving anyclass instance Plated Schema

instance ToJSON Schema where
  toJSON = \case
    SchemaInteger info MkIntegerSchema{..} ->
      dataType info "integer"
        & optionalField "multipleOf" multipleOf
        & optionalField "minimum" minimum
        & optionalField "maximum" maximum
        & optionalField "exclusiveMinimum" exclusiveMinimum
        & optionalField "exclusiveMaximum" exclusiveMaximum
        & Aeson.Object
    SchemaBytes info MkBytesSchema{..} ->
      dataType info "bytes"
        & optionalField "enum" (fmap toHex <$> nonEmpty enum)
        & optionalField "maxLength" maxLength
        & optionalField "minLength" minLength
        & Aeson.Object
     where
      toHex :: ByteString -> Text
      toHex = Text.decodeUtf8 . Base16.encode
    SchemaList info MkListSchema{..} ->
      dataType info "list"
        & requiredField "items" schema
        & optionalField "minItems" minItems
        & optionalField "maxItems" maxItems
        & optionalField "uniqueItems" unique
        & Aeson.Object
    SchemaMap info MkMapSchema{..} ->
      dataType info "map"
        & requiredField "keys" keySchema
        & requiredField "values" valueSchema
        & optionalField "minItems" minItems
        & optionalField "maxItems" maxItems
        & Aeson.Object
    SchemaConstructor info MkConstructorSchema{..} ->
      dataType info "constructor"
        & requiredField "index" index
        & optionalField "fields" (nonEmpty fieldSchemas)
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
    SchemaBuiltInPair info MkPairSchema{left, right} ->
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
    infoFields MkSchemaInfo{title, description, comment} =
      KeyMap.empty
        & optionalField "title" title
        & optionalField "description" description
        & optionalField "$comment" comment

-- | Additional information optionally attached to any datatype schema definition.
data SchemaInfo = MkSchemaInfo
  { title       :: Maybe String
  , description :: Maybe String
  , comment     :: Maybe String
  }
  deriving stock (Eq, Show, Generic, Data)

emptySchemaInfo :: SchemaInfo
emptySchemaInfo = MkSchemaInfo{title = Nothing, description = Nothing, comment = Nothing}

data IntegerSchema = MkIntegerSchema
  { multipleOf       :: Maybe Integer
  -- ^ An instance is valid if division by this value results in an integer.
  , minimum          :: Maybe Integer
  -- ^ An instance is valid only if it is greater than or exactly equal to "minimum".
  , maximum          :: Maybe Integer
  -- ^ An instance is valid only if it is less than or exactly equal to "maximum".
  , exclusiveMinimum :: Maybe Integer
  -- ^ An instance is valid only if it is strictly greater than "exclusiveMinimum".
  , exclusiveMaximum :: Maybe Integer
  -- ^ An instance is valid only if it is strictly less than "exclusiveMaximum".
  }
  deriving stock (Eq, Show, Generic, Data)

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
  { enum      :: [ByteString]
  -- ^ An instance validates successfully if once hex-encoded,
  -- its value matches one of the specified values.
  , minLength :: Maybe Natural
  -- ^ An instance is valid if its length is greater than, or equal to, this value.
  , maxLength :: Maybe Natural
  -- ^ An instance is valid if its length is less than, or equal to, this value.
  }
  deriving stock (Eq, Show, Generic, Data)

emptyBytesSchema :: BytesSchema
emptyBytesSchema = MkBytesSchema{enum = [], minLength = Nothing, maxLength = Nothing}

data ListSchema = MkListSchema
  { schema   :: Schema
  -- ^ Element schema
  , minItems :: Maybe Natural
  -- ^ An array instance is valid if its size is greater than, or equal to, this value.
  , maxItems :: Maybe Natural
  -- ^ An array instance is valid if its size is less than, or equal to, this value.
  , unique   :: Maybe Bool
  -- ^ If this value is false, the instance validates successfully.
  -- If it is set to True, the instance validates successfully if all of its elements are unique.
  }
  deriving stock (Eq, Show, Generic, Data)

mkListSchema :: Schema -> ListSchema
mkListSchema schema = MkListSchema{schema, minItems = Nothing, maxItems = Nothing, unique = Nothing}

data MapSchema = MkMapSchema
  { keySchema   :: Schema
  -- ^ Key schema
  , valueSchema :: Schema
  -- ^ Value schema
  , minItems    :: Maybe Natural
  -- ^ A map instance is valid if its size is greater than, or equal to, this value.
  , maxItems    :: Maybe Natural
  -- ^ A map instance is valid if its size is less than, or equal to, this value.
  }
  deriving stock (Eq, Show, Generic, Data)

data ConstructorSchema = MkConstructorSchema
  { index        :: Natural
  -- ^ Constructor index
  , fieldSchemas :: [Schema]
  -- ^ Field schemas
  }
  deriving stock (Eq, Show, Generic, Data)

data PairSchema = MkPairSchema
  { left  :: Schema
  -- ^ Schema of the first element
  , right :: Schema
  -- ^ Schema of the second element
  }
  deriving stock (Eq, Show, Generic, Data)
