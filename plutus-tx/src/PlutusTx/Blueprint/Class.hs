{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}

module PlutusTx.Blueprint.Class where

import Prelude hiding (maximum, minimum)

import Data.Kind (Type)
import PlutusTx.Blueprint.Schema (PairSchema (..), Schema (..), emptyBytesSchema,
                                  emptyIntegerSchema, emptySchemaInfo)
import PlutusTx.Builtins (BuiltinByteString, BuiltinData, BuiltinString)

{- |
  A class of types that have a Blueprint schema definition
  and can reference other schema definitions of other types.
-}
class HasDataSchema (t :: Type) (referencedTypes :: [Type]) where
  dataSchema :: Schema referencedTypes

instance HasDataSchema () ts where
  dataSchema = SchemaBuiltInUnit emptySchemaInfo

instance HasDataSchema Integer ts where
  dataSchema = SchemaInteger emptySchemaInfo emptyIntegerSchema

instance HasDataSchema BuiltinByteString ts where
  dataSchema = SchemaBytes emptySchemaInfo emptyBytesSchema

instance HasDataSchema Bool ts where
  dataSchema = SchemaBuiltInBoolean emptySchemaInfo

instance HasDataSchema BuiltinString ts where
  dataSchema = SchemaBuiltInString emptySchemaInfo

instance HasDataSchema BuiltinData ts where
  dataSchema = SchemaBuiltInData emptySchemaInfo

instance (HasDataSchema a ts, HasDataSchema b ts) => HasDataSchema (a, b) ts where
  dataSchema =
    SchemaBuiltInPair
      emptySchemaInfo
      MkPairSchema{left = dataSchema @a @ts, right = dataSchema @b @ts}

instance (HasDataSchema a ts) => HasDataSchema [a] ts where
  dataSchema = SchemaBuiltInList emptySchemaInfo (dataSchema @a @ts)
