{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusTx.Blueprint.Class where

import Prelude hiding (maximum, minimum)

import Data.ByteString (ByteString)
import Data.Kind (Type)
import PlutusTx.Blueprint.Schema (ListSchema (..), PairSchema (..), Schema (..), emptyBytesSchema,
                                  emptyIntegerSchema)
import PlutusTx.Blueprint.Schema.Annotation (emptySchemaInfo)
import PlutusTx.Builtins (BuiltinByteString, BuiltinData, BuiltinString)
import PlutusTx.Builtins.Internal (BuiltinList, BuiltinPair, BuiltinUnit)

{-|
  A class of types that have a Blueprint schema definition
  and can reference other schema definitions of other types.
-}
class HasBlueprintSchema (t :: Type) (referencedTypes :: [Type]) where
  schema :: Schema referencedTypes

instance HasBlueprintSchema Int referencedTypes where
  schema = SchemaInteger emptySchemaInfo emptyIntegerSchema

instance HasBlueprintSchema Integer referencedTypes where
  schema = SchemaInteger emptySchemaInfo emptyIntegerSchema

instance HasBlueprintSchema BuiltinData referencedTypes where
  schema = SchemaBuiltInData emptySchemaInfo

instance HasBlueprintSchema BuiltinUnit referencedTypes where
  schema = SchemaBuiltInUnit emptySchemaInfo

instance HasBlueprintSchema BuiltinString referencedTypes where
  schema = SchemaBuiltInString emptySchemaInfo

instance HasBlueprintSchema BuiltinByteString referencedTypes where
  schema = SchemaBytes emptySchemaInfo emptyBytesSchema

instance HasBlueprintSchema ByteString referencedTypes where
  schema = SchemaBytes emptySchemaInfo emptyBytesSchema

instance
  (HasBlueprintSchema a referencedTypes)
  => HasBlueprintSchema [a] referencedTypes
  where
  schema =
    SchemaList
      emptySchemaInfo
      ( MkListSchema
          { minItems = Nothing
          , maxItems = Nothing
          , uniqueItems = Nothing
          , itemSchema = schema @a
          }
      )

instance
  (HasBlueprintSchema a referencedTypes)
  => HasBlueprintSchema (BuiltinList a) referencedTypes
  where
  schema = SchemaBuiltInList emptySchemaInfo (schema @a)

instance
  ( HasBlueprintSchema a referencedTypes
  , HasBlueprintSchema b referencedTypes
  )
  => HasBlueprintSchema (BuiltinPair a b) referencedTypes
  where
  schema = SchemaBuiltInPair emptySchemaInfo (MkPairSchema (schema @a) (schema @b))
