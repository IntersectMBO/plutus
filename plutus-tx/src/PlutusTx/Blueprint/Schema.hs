{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}

module PlutusTx.Blueprint.Schema where

import Data.Aeson (ToJSON (..), (.=))
import Data.Aeson qualified as Aeson
import Data.ByteString (ByteString)
import Data.ByteString.Base16 qualified as Base16
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe (catMaybes)
import Data.Text (Text)
import Data.Text.Encoding qualified as Text
import Numeric.Natural (Natural)
import Prelude

data DataSchema
  = DSInteger
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
  | DSBytes
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
  | DSList
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
      -- | Element schema
      DataSchema
      -- | Minimum number of elements
      (Maybe Natural)
      -- | Maximum number of elements
      (Maybe Natural)
  | DSMap
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
      -- | Key schema
      DataSchema
      -- | Value schema
      DataSchema
      -- | Minimum number of elements
      (Maybe Natural)
      -- | Maximum number of elements
      (Maybe Natural)
  | DSConstructor
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
      -- | Constructor index
      Natural
      -- | Field schemas
      [DataSchema]
  | DSBuiltInData
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
  | DSBuiltInUnit
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
  | DSBuiltInBoolean
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
  | DSBuiltInInteger
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
  | DSBuiltInBytes
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
  | DSBuiltInString
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
  | DSBuiltInPair
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
      -- | Schema of the first element
      DataSchema
      -- | Schema of the second element
      DataSchema
  | DSBuiltInList
      -- | Title
      (Maybe String)
      -- | Description
      (Maybe String)
      -- | Comment
      (Maybe String)
      -- | Element schema
      DataSchema
  | DSOneOf (NonEmpty DataSchema)
  | DSAnyOf (NonEmpty DataSchema)
  | DSAllOf (NonEmpty DataSchema)
  | DSNot DataSchema
  deriving stock (Show)

instance ToJSON DataSchema where
  toJSON = \case
    DSInteger title description comment ->
      dataType title description comment "integer"
    DSBytes title description comment enum maxLength minLength ->
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
    DSList title description comment schema minItems maxItems ->
      Aeson.object
        $ catMaybes
          [ Just $ "dataType" .= ("list" :: String)
          , Just $ "items" .= schema
          , fmap ("minItems" .=) minItems
          , fmap ("maxItems" .=) maxItems
          , fmap ("title" .=) title
          , fmap ("description" .=) description
          , fmap ("$comment" .=) comment
          ]
    DSMap title description comment keySchema valueSchema minItems maxItems ->
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
    DSConstructor title description comment index fieldSchemas ->
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
    DSBuiltInData title description comment ->
      Aeson.object
        $ catMaybes
          [ fmap ("title" .=) title
          , fmap ("description" .=) description
          , fmap ("$comment" .=) comment
          ]
    DSBuiltInUnit title description comment ->
      dataType title description comment "#unit"
    DSBuiltInBoolean title description comment ->
      dataType title description comment "#boolean"
    DSBuiltInInteger title description comment ->
      dataType title description comment "#integer"
    DSBuiltInBytes title description comment ->
      dataType title description comment "#bytes"
    DSBuiltInString title description comment ->
      dataType title description comment "#string"
    DSBuiltInPair title description comment schema1 schema2 ->
      -- TODO (Yura): double check the encoding of a Pair
      Aeson.object
        $ catMaybes
          [ Just $ "dataType" .= ("#pair" :: String)
          , Just $ "fst" .= schema1
          , Just $ "snd" .= schema2
          , fmap ("title" .=) title
          , fmap ("description" .=) description
          , fmap ("$comment" .=) comment
          ]
    DSBuiltInList title description comment schema ->
      Aeson.object
        $ catMaybes
          [ Just $ "dataType" .= ("#list" :: String)
          , Just $ "items" .= schema
          , fmap ("title" .=) title
          , fmap ("description" .=) description
          , fmap ("$comment" .=) comment
          ]
    DSOneOf schemas -> Aeson.object ["oneOf" .= schemas]
    DSAnyOf schemas -> Aeson.object ["anyOf" .= schemas]
    DSAllOf schemas -> Aeson.object ["allOf" .= schemas]
    DSNot schema -> Aeson.object ["not" .= schema]
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

----------------------------------------------------------------------------------------------------
-- Convenience constructors ------------------------------------------------------------------------

dsInteger :: DataSchema
dsInteger =
  DSInteger
    Nothing -- Title
    Nothing -- Description
    Nothing -- Comment

dsBytes :: DataSchema
dsBytes =
  DSBytes
    Nothing -- Title
    Nothing -- Description
    Nothing -- Comment
    [] -- Enum
    Nothing -- Min length
    Nothing -- Max length

dsList :: DataSchema -> DataSchema
dsList itemSchema =
  DSList
    Nothing -- Title
    Nothing -- Description
    Nothing -- Comment
    itemSchema
    Nothing -- Min items
    Nothing -- Max items

dsMap :: DataSchema -> DataSchema -> DataSchema
dsMap keySchema valueSchema =
  DSMap
    Nothing -- Title
    Nothing -- Description
    Nothing -- Comment
    keySchema
    valueSchema
    Nothing -- Min items
    Nothing -- Max items

dsConstructor :: Natural -> [DataSchema] -> DataSchema
dsConstructor =
  DSConstructor
    Nothing -- Title
    Nothing -- Description
    Nothing -- Comment

dsBuiltInData :: DataSchema
dsBuiltInData =
  DSBuiltInData
    Nothing -- Title
    Nothing -- Description
    Nothing -- Comment

dsBuiltInUnit :: DataSchema
dsBuiltInUnit =
  DSBuiltInUnit
    Nothing -- Title
    Nothing -- Description
    Nothing -- Comment

dsBuiltInBoolean :: DataSchema
dsBuiltInBoolean =
  DSBuiltInBoolean
    Nothing -- Title
    Nothing -- Description
    Nothing -- Comment

dsBuiltInInteger :: DataSchema
dsBuiltInInteger =
  DSBuiltInInteger
    Nothing -- Title
    Nothing -- Description
    Nothing -- Comment

dsBuiltInBytes :: DataSchema
dsBuiltInBytes =
  DSBuiltInBytes
    Nothing -- Title
    Nothing -- Description
    Nothing -- Comment

dsBuiltInString :: DataSchema
dsBuiltInString =
  DSBuiltInString
    Nothing -- Title
    Nothing -- Description
    Nothing -- Comment

dsBuiltInPair :: DataSchema -> DataSchema -> DataSchema
dsBuiltInPair =
  DSBuiltInPair
    Nothing -- Title
    Nothing -- Description
    Nothing -- Comment

dsBuiltInList :: DataSchema -> DataSchema
dsBuiltInList =
  DSBuiltInList
    Nothing -- Title
    Nothing -- Description
    Nothing -- Comment

----------------------------------------------------------------------------------------------------
-- Modifiers ---------------------------------------------------------------------------------------

setTitle :: String -> DataSchema -> DataSchema
setTitle title = \case
  DSInteger _ d c -> DSInteger (Just title) d c
  DSBytes _ d c enum minLength maxLength -> DSBytes (Just title) d c enum minLength maxLength
  DSList _ d c s minItems maxItems -> DSList (Just title) d c s minItems maxItems
  DSMap _ d c k v minItems maxItems -> DSMap (Just title) d c k v minItems maxItems
  DSConstructor _ d c i fs -> DSConstructor (Just title) d c i fs
  DSBuiltInData _ d c -> DSBuiltInData (Just title) d c
  DSBuiltInUnit _ d c -> DSBuiltInUnit (Just title) d c
  DSBuiltInBoolean _ d c -> DSBuiltInBoolean (Just title) d c
  DSBuiltInInteger _ d c -> DSBuiltInInteger (Just title) d c
  DSBuiltInBytes _ d c -> DSBuiltInBytes (Just title) d c
  DSBuiltInString _ d c -> DSBuiltInString (Just title) d c
  DSBuiltInPair _ d c s1 s2 -> DSBuiltInPair (Just title) d c s1 s2
  DSBuiltInList _ d c s -> DSBuiltInList (Just title) d c s
  x@DSOneOf{} -> x
  x@DSAnyOf{} -> x
  x@DSAllOf{} -> x
  x@DSNot{} -> x

setDescription :: String -> DataSchema -> DataSchema
setDescription description = \case
  DSInteger t _ c -> DSInteger t (Just description) c
  DSBytes t _ c enum minLength maxLength -> DSBytes t (Just description) c enum minLength maxLength
  DSList t _ c s minItems maxItems -> DSList t (Just description) c s minItems maxItems
  DSMap t _ c k v minItems maxItems -> DSMap t (Just description) c k v minItems maxItems
  DSConstructor t _ c i fs -> DSConstructor t (Just description) c i fs
  DSBuiltInData t _ c -> DSBuiltInData t (Just description) c
  DSBuiltInUnit t _ c -> DSBuiltInUnit t (Just description) c
  DSBuiltInBoolean t _ c -> DSBuiltInBoolean t (Just description) c
  DSBuiltInInteger t _ c -> DSBuiltInInteger t (Just description) c
  DSBuiltInBytes t _ c -> DSBuiltInBytes t (Just description) c
  DSBuiltInString t _ c -> DSBuiltInString t (Just description) c
  DSBuiltInPair t _ c s1 s2 -> DSBuiltInPair t (Just description) c s1 s2
  DSBuiltInList t _ c s -> DSBuiltInList t (Just description) c s
  x@DSOneOf{} -> x
  x@DSAnyOf{} -> x
  x@DSAllOf{} -> x
  x@DSNot{} -> x

setComment :: String -> DataSchema -> DataSchema
setComment comment = \case
  DSInteger t d _ -> DSInteger t d (Just comment)
  DSBytes t d _ enum minLength maxLength -> DSBytes t d (Just comment) enum minLength maxLength
  DSList t d _ s minItems maxItems -> DSList t d (Just comment) s minItems maxItems
  DSMap t d _ k v minItems maxItems -> DSMap t d (Just comment) k v minItems maxItems
  DSConstructor t d _ i fs -> DSConstructor t d (Just comment) i fs
  DSBuiltInData t d _ -> DSBuiltInData t d (Just comment)
  DSBuiltInUnit t d _ -> DSBuiltInUnit t d (Just comment)
  DSBuiltInBoolean t d _ -> DSBuiltInBoolean t d (Just comment)
  DSBuiltInInteger t d _ -> DSBuiltInInteger t d (Just comment)
  DSBuiltInBytes t d _ -> DSBuiltInBytes t d (Just comment)
  DSBuiltInString t d _ -> DSBuiltInString t d (Just comment)
  DSBuiltInPair t d _ s1 s2 -> DSBuiltInPair t d (Just comment) s1 s2
  DSBuiltInList t d _ s -> DSBuiltInList t d (Just comment) s
  x@DSOneOf{} -> x
  x@DSAnyOf{} -> x
  x@DSAllOf{} -> x
  x@DSNot{} -> x

setMinLength :: Natural -> DataSchema -> DataSchema
setMinLength minLength = \case
  DSBytes t d c enum _minLength maxLength -> DSBytes t d c enum (Just minLength) maxLength
  x -> x

setMaxLength :: Natural -> DataSchema -> DataSchema
setMaxLength maxLength = \case
  DSBytes t d c enum minLen _maxLen -> DSBytes t d c enum minLen (Just maxLength)
  x -> x
