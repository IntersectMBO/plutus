{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE DerivingStrategies       #-}
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module PlutusTx.Blueprint.Schema where

import Data.Aeson (ToJSON (..), (.=))
import Data.Aeson qualified as Aeson
import Data.ByteString (ByteString)
import Data.ByteString.Base16 qualified as Base16
import Data.Kind (Constraint)
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe (catMaybes)
import Data.Proxy (Proxy (..))
import Data.Text (Text)
import Data.Text.Encoding qualified as Text
import Data.Typeable (Typeable, typeRep)
import GHC.TypeLits qualified as GHC
import Numeric.Natural (Natural)
import PlutusTx.Builtins (BuiltinByteString, BuiltinData, BuiltinString)
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
  | SchemaRef String
  deriving stock (Show)

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
          , Just $ "constructor" .= index
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
          , Just $ "fst" .= schema1
          , Just $ "snd" .= schema2
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
    SchemaRef ref -> Aeson.object ["$ref" .= ("#/definitions/" ++ ref)]
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

type HasSchemaDefinition :: forall a. a -> [a] -> Constraint
type family HasSchemaDefinition n xs where
  HasSchemaDefinition n '[] =
    GHC.TypeError
      ( GHC.ShowType n
          GHC.:<>: GHC.Text " schema was not found in the list of schema definitions."
      )
  HasSchemaDefinition () _ = ()
  HasSchemaDefinition Integer _ = ()
  HasSchemaDefinition BuiltinData _ = ()
  HasSchemaDefinition BuiltinString _ = ()
  HasSchemaDefinition BuiltinByteString _ = ()
  HasSchemaDefinition x (x ': xs) = ()
  HasSchemaDefinition x (_ ': xs) = HasSchemaDefinition x xs

schemaRef :: forall typ schemas. (Typeable typ, HasSchemaDefinition typ schemas) => Schema
schemaRef = SchemaRef $ show $ typeRep $ Proxy @typ

----------------------------------------------------------------------------------------------------
-- Modifiers ---------------------------------------------------------------------------------------

setTitle :: String -> Schema -> Schema
setTitle title = \case
  SchemaInteger _ d c mlt max eMax min eMin ->
    SchemaInteger (Just title) d c mlt max eMax min eMin
  SchemaBytes _ d c enum minLength maxLength ->
    SchemaBytes (Just title) d c enum minLength maxLength
  SchemaList _ d c s minItems maxItems unique ->
    SchemaList (Just title) d c s minItems maxItems unique
  SchemaMap _ d c k v minItems maxItems ->
    SchemaMap (Just title) d c k v minItems maxItems
  SchemaConstructor _ d c i fs ->
    SchemaConstructor (Just title) d c i fs
  SchemaBuiltInData _ d c ->
    SchemaBuiltInData (Just title) d c
  SchemaBuiltInUnit _ d c ->
    SchemaBuiltInUnit (Just title) d c
  SchemaBuiltInBoolean _ d c ->
    SchemaBuiltInBoolean (Just title) d c
  SchemaBuiltInInteger _ d c ->
    SchemaBuiltInInteger (Just title) d c
  SchemaBuiltInBytes _ d c ->
    SchemaBuiltInBytes (Just title) d c
  SchemaBuiltInString _ d c ->
    SchemaBuiltInString (Just title) d c
  SchemaBuiltInPair _ d c s1 s2 ->
    SchemaBuiltInPair (Just title) d c s1 s2
  SchemaBuiltInList _ d c s ->
    SchemaBuiltInList (Just title) d c s
  x@SchemaOneOf{} -> x
  x@SchemaAnyOf{} -> x
  x@SchemaAllOf{} -> x
  x@SchemaNot{} -> x
  x@SchemaRef{} -> x

setDescription :: String -> Schema -> Schema
setDescription description = \case
  SchemaInteger t _ c mlt max eMax min eMin ->
    SchemaInteger t (Just description) c mlt max eMax min eMin
  SchemaBytes t _ c enum minLength maxLength ->
    SchemaBytes t (Just description) c enum minLength maxLength
  SchemaList t _ c s min max unique ->
    SchemaList t (Just description) c s min max unique
  SchemaMap t _ c k v min max ->
    SchemaMap t (Just description) c k v min max
  SchemaConstructor t _ c i fs ->
    SchemaConstructor t (Just description) c i fs
  SchemaBuiltInData t _ c ->
    SchemaBuiltInData t (Just description) c
  SchemaBuiltInUnit t _ c ->
    SchemaBuiltInUnit t (Just description) c
  SchemaBuiltInBoolean t _ c ->
    SchemaBuiltInBoolean t (Just description) c
  SchemaBuiltInInteger t _ c ->
    SchemaBuiltInInteger t (Just description) c
  SchemaBuiltInBytes t _ c ->
    SchemaBuiltInBytes t (Just description) c
  SchemaBuiltInString t _ c ->
    SchemaBuiltInString t (Just description) c
  SchemaBuiltInPair t _ c s1 s2 ->
    SchemaBuiltInPair t (Just description) c s1 s2
  SchemaBuiltInList t _ c s ->
    SchemaBuiltInList t (Just description) c s
  x@SchemaOneOf{} -> x
  x@SchemaAnyOf{} -> x
  x@SchemaAllOf{} -> x
  x@SchemaNot{} -> x
  x@SchemaRef{} -> x

setComment :: String -> Schema -> Schema
setComment comment = \case
  SchemaInteger t d _ mlt max eMax min eMin ->
    SchemaInteger t d (Just comment) mlt max eMax min eMin
  SchemaBytes t d _ enum minLength maxLength ->
    SchemaBytes t d (Just comment) enum minLength maxLength
  SchemaList t d _ s min max unique ->
    SchemaList t d (Just comment) s min max unique
  SchemaMap t d _ k v min max ->
    SchemaMap t d (Just comment) k v min max
  SchemaConstructor t d _ i fs ->
    SchemaConstructor t d (Just comment) i fs
  SchemaBuiltInData t d _ ->
    SchemaBuiltInData t d (Just comment)
  SchemaBuiltInUnit t d _ ->
    SchemaBuiltInUnit t d (Just comment)
  SchemaBuiltInBoolean t d _ ->
    SchemaBuiltInBoolean t d (Just comment)
  SchemaBuiltInInteger t d _ ->
    SchemaBuiltInInteger t d (Just comment)
  SchemaBuiltInBytes t d _ ->
    SchemaBuiltInBytes t d (Just comment)
  SchemaBuiltInString t d _ ->
    SchemaBuiltInString t d (Just comment)
  SchemaBuiltInPair t d _ s1 s2 ->
    SchemaBuiltInPair t d (Just comment) s1 s2
  SchemaBuiltInList t d _ s ->
    SchemaBuiltInList t d (Just comment) s
  x@SchemaOneOf{} -> x
  x@SchemaAnyOf{} -> x
  x@SchemaAllOf{} -> x
  x@SchemaNot{} -> x
  x@SchemaRef{} -> x

setMinLength :: Natural -> Schema -> Schema
setMinLength minLength = \case
  SchemaBytes t d c enum _minLength maxLength -> SchemaBytes t d c enum (Just minLength) maxLength
  x -> x

setMaxLength :: Natural -> Schema -> Schema
setMaxLength maxLength = \case
  SchemaBytes t d c enum minLen _maxLen -> SchemaBytes t d c enum minLen (Just maxLength)
  x -> x
