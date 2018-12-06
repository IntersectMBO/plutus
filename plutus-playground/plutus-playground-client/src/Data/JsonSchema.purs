module Data.JsonSchema where

import Prelude

import Control.Alt ((<|>))
import Data.Maybe (Maybe(..))
import Debug.Trace as Debug
-- import Foreign (F, ForeignError(ForeignError), fail, readString)
-- import Foreign.Class (class Decode, decode)
-- import Foreign.Index (readProp)
-- import Foreign.Object (Object)
-- import Simple.JSON (class ReadForeign)
import Data.Generic (class Generic)

newtype Schema = Schema
  { _type :: Maybe TypeValidator
  , additionalProperties :: Maybe Schema
  , description :: Maybe String
  , format :: Maybe String
  , items :: Maybe Schema
  , oneOf :: Maybe (Array Schema)
  , properties :: Maybe Schema
  , ref :: Maybe SchemaRef
  , required :: Maybe (Array String)
  }

derive instance genericSchema :: Generic Schema

-- instance readForeignSchema :: ReadForeign Schema where
--   readImpl = decode
-- instance decodeSchema :: Decode Schema where
--   decode f = do
--     _type <- readProp "type" f >>= decode
--     additionalProperties <- readProp "additionalProperties" f >>= decode
--     description <- readProp "description" f >>= decode
--     format <- readProp "format" f >>= decode
--     items <- readProp "items" f >>= decode
--     oneOf <- readProp "oneOf" f >>= decode
--     properties <- readProp "properties" f >>= decode
--     ref <- readProp "$ref" f >>= decode
--     required <- readProp "required" f >>= decode
--     pure $ Schema { _type, additionalProperties, description, format, items, oneOf, properties, ref, required }
-- instance showSchema :: Show Schema where
--   show (Schema { _type, additionalProperties, description, format, items, oneOf, properties, ref, required }) =
--     "{\n  type: " <> show _type <>
--     ",\n  additionalProperties: " <> show additionalProperties <>
--     ",\n  description: " <> show description <>
--     ",\n  format: " <> show format <>
--     ",\n  items: " <> show items <>
--     ",\n  oneOf: " <> show oneOf <>
--     ",\n  properties: " <> show properties <>
--     ",\n  ref: " <> show ref <>
--     ",\n  required: " <> show required <> "}"

newtype SchemaRef = SchemaRef String
-- instance decodeSchemaRef :: Decode SchemaRef where
--   decode f = SchemaRef <$> decode f
-- instance showSchemaRef :: Show SchemaRef where
--   show (SchemaRef ref) = show ref

derive instance genericSchemaRef :: Generic SchemaRef

data TypeValidator = TypeValidatorString SchemaType | TypeValidatorArray (Array SchemaType)

derive instance genericTypeValidator :: Generic TypeValidator
-- instance decodeTypeValidator :: Decode TypeValidator where
--   decode f = parseArray <|> parseSingle
--     where
--       parseArray = TypeValidatorArray <$> (decode f :: F (Array SchemaType))
--       parseSingle = TypeValidatorString <$> (decode f :: F SchemaType)
-- instance showTypeValidator :: Show TypeValidator where
--   show (TypeValidatorArray arr) = show arr
--   show (TypeValidatorString s) = show s

data SchemaType
  = SchemaObject
  | SchemaArray
  | SchemaString
  | SchemaNumber
  | SchemaInteger
  | SchemaBoolean
  | SchemaNull

derive instance genericSchemaType :: Generic SchemaType
-- instance decodeSchemaType :: Decode SchemaType where
--   decode f = do
--     decoded <- readString f
--     case decoded of
--       "object" -> pure SchemaObject
--       "array" -> pure SchemaArray
--       "string" -> pure SchemaString
--       "number" -> pure SchemaNumber
--       "integer" -> pure SchemaInteger
--       "boolean" -> pure SchemaBoolean
--       "null" -> pure SchemaNull
--       _ -> fail (ForeignError $ "Could not decode value '" <> "' as type SchemaType")
-- instance showSchemaType :: Show SchemaType where
--   show SchemaObject = "\"object\""
--   show SchemaArray = "\"array\""
--   show SchemaString = "\"string\""
--   show SchemaNumber = "\"number\""
--   show SchemaInteger = "\"integer\""
--   show SchemaBoolean = "\"boolean\""
--   show SchemaNull = "\"null\""
-- instance eqSchemaType :: Eq SchemaType where
--   eq SchemaObject SchemaObject = true
--   eq SchemaArray SchemaArray = true
--   eq SchemaString SchemaString = true
--   eq SchemaNumber SchemaNumber = true
--   eq SchemaInteger SchemaInteger = true
--   eq SchemaBoolean SchemaBoolean = true
--   eq SchemaNull SchemaNull = true
--   eq _ _ = false
