{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module PlutusTx.Blueprint.Schema where

import Control.Lens.Plated (Plated)
import Data.Aeson (ToJSON (..), (.=))
import Data.Aeson qualified as Aeson
import Data.ByteString (ByteString)
import Data.ByteString.Base16 qualified as Base16
import Data.Data (Data)
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe (catMaybes)
import Data.Text (Text)
import Data.Text.Encoding qualified as Text
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import PlutusTx.Blueprint.Definition.Id (DefinitionId, definitionIdToText)
import Prelude hiding (max, min)

data Schema
  = SchemaInteger
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
      -- | Multiple of
      (Maybe Integer)
      -- | Maximum
      (Maybe Integer)
      -- | Exclusive maximum
      (Maybe Integer)
      -- | Minimum
      (Maybe Integer)
      -- | Exclusive minimum
      (Maybe Integer)
  | SchemaBytes
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
      -- | Allowed values (enumeration)
      [ByteString]
      -- | Max length in bytes
      (Maybe Natural)
      -- | Min length in bytes
      (Maybe Natural)
  | SchemaList
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
      -- | Element schema
      Schema
      -- | Minimum number of elements
      (Maybe Natural)
      -- | Maximum number of elements
      (Maybe Natural)
      -- | Unique elements
      (Maybe Bool)
  | SchemaMap
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
      -- | Key schema
      Schema
      -- | Value schema
      Schema
      -- | Minimum number of elements
      (Maybe Natural)
      -- | Maximum number of elements
      (Maybe Natural)
  | SchemaConstructor
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
      -- | Constructor index
      Natural
      -- | Field schemas
      [Schema]
  | SchemaBuiltInData
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
  | SchemaBuiltInUnit
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
  | SchemaBuiltInBoolean
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
  | SchemaBuiltInInteger
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
  | SchemaBuiltInBytes
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
  | SchemaBuiltInString
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
  | SchemaBuiltInPair
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
      -- | Schema of the first element
      Schema
      -- | Schema of the second element
      Schema
  | SchemaBuiltInList
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
      -- | Element schema
      Schema
  | SchemaOneOf (NonEmpty Schema)
  | SchemaAnyOf (NonEmpty Schema)
  | SchemaAllOf (NonEmpty Schema)
  | SchemaNot Schema
  | SchemaDefinitionRef DefinitionId
  deriving stock (Eq, Show, Generic, Data)
  deriving anyclass (Plated)

instance ToJSON Schema where
  toJSON = \case
    SchemaInteger title description comment multiple max eMax min eMin ->
      Aeson.object
        $ catMaybes
          [ Just $ "dataType" .= ("integer" :: String)
          , fmap ("title" .=) title
          , fmap ("description" .=) description
          , fmap ("$comment" .=) comment
          , fmap ("multipleOf" .=) multiple
          , fmap ("maximum" .=) max
          , fmap ("exclusiveMaximum" .=) eMax
          , fmap ("minimum" .=) min
          , fmap ("exclusiveMinimum" .=) eMin
          ]
    SchemaBytes title description comment enum maxLength minLength ->
      Aeson.object
        $ catMaybes
          [ Just $ "dataType" .= ("bytes" :: String)
          , fmap ("minLength" .=) minLength
          , fmap ("maxLength" .=) maxLength
          , case enum of
              [] -> Nothing
              xs -> Just $ "enum" .= fmap toHex xs
          , fmap ("title" .=) title
          , fmap ("description" .=) description
          , fmap ("$comment" .=) comment
          ]
     where
      toHex :: ByteString -> Text
      toHex = Text.decodeUtf8 . Base16.encode
    SchemaList title description comment schema minItems maxItems unique ->
      Aeson.object
        $ catMaybes
          [ Just $ "dataType" .= ("list" :: String)
          , Just $ "items" .= schema
          , fmap ("minItems" .=) minItems
          , fmap ("maxItems" .=) maxItems
          , fmap ("uniqueItems" .=) unique
          , fmap ("title" .=) title
          , fmap ("description" .=) description
          , fmap ("$comment" .=) comment
          ]
    SchemaMap title description comment keySchema valueSchema minItems maxItems ->
      Aeson.object
        $ catMaybes
          [ Just $ "dataType" .= ("map" :: String)
          , Just $ "keys" .= keySchema
          , Just $ "values" .= valueSchema
          , fmap ("minItems" .=) minItems
          , fmap ("maxItems" .=) maxItems
          , fmap ("title" .=) title
          , fmap ("description" .=) description
          , fmap ("$comment" .=) comment
          ]
    SchemaConstructor title description comment index fieldSchemas ->
      Aeson.object
        $ catMaybes
          [ Just ("dataType" .= ("constructor" :: String))
          , Just $ "index" .= index
          , case fieldSchemas of
              [] -> Nothing
              xs -> Just $ "fields" .= xs
          , fmap ("title" .=) title
          , fmap ("description" .=) description
          , fmap ("$comment" .=) comment
          ]
    SchemaBuiltInData title description comment ->
      Aeson.object
        $ catMaybes
          [ fmap ("title" .=) title
          , fmap ("description" .=) description
          , fmap ("$comment" .=) comment
          ]
    SchemaBuiltInUnit title description comment ->
      dataType title description comment "#unit"
    SchemaBuiltInBoolean title description comment ->
      dataType title description comment "#boolean"
    SchemaBuiltInInteger title description comment ->
      dataType title description comment "#integer"
    SchemaBuiltInBytes title description comment ->
      dataType title description comment "#bytes"
    SchemaBuiltInString title description comment ->
      dataType title description comment "#string"
    SchemaBuiltInPair title description comment schema1 schema2 ->
      Aeson.object
        $ catMaybes
          [ Just $ "dataType" .= ("#pair" :: String)
          , Just $ "left" .= schema1
          , Just $ "right" .= schema2
          , fmap ("title" .=) title
          , fmap ("description" .=) description
          , fmap ("$comment" .=) comment
          ]
    SchemaBuiltInList title description comment schema ->
      Aeson.object
        $ catMaybes
          [ Just $ "dataType" .= ("#list" :: String)
          , Just $ "items" .= schema
          , fmap ("title" .=) title
          , fmap ("description" .=) description
          , fmap ("$comment" .=) comment
          ]
    SchemaOneOf schemas -> Aeson.object ["oneOf" .= schemas]
    SchemaAnyOf schemas -> Aeson.object ["anyOf" .= schemas]
    SchemaAllOf schemas -> Aeson.object ["allOf" .= schemas]
    SchemaNot schema -> Aeson.object ["not" .= schema]
    SchemaDefinitionRef definitionId ->
      Aeson.object ["$ref" .= ("#/definitions/" <> definitionIdToText definitionId)]
   where
    dataType :: Maybe String -> Maybe String -> Maybe String -> String -> Aeson.Value
    dataType title description comment ty =
      Aeson.object
        $ catMaybes
          [ Just $ "dataType" .= ty
          , fmap ("title" .=) title
          , fmap ("description" .=) description
          , fmap ("$comment" .=) comment
          ]
