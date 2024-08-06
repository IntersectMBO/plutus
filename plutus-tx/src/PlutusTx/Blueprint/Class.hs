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
                                  emptyIntegerSchema)
import PlutusTx.Blueprint.Schema.Annotation (emptySchemaInfo)
import PlutusTx.Builtins (BuiltinByteString, BuiltinData, BuiltinString)

{- |
  A class of types that have a Blueprint schema definition
  and can reference other schema definitions of other types.
-}
class HasSchema (t :: Type) (referencedTypes :: [Type]) where
  schema :: Schema referencedTypes

instance HasSchema () ts where
  schema = SchemaBuiltInUnit emptySchemaInfo

instance HasSchema Integer ts where
  schema = SchemaInteger emptySchemaInfo emptyIntegerSchema

instance HasSchema BuiltinByteString ts where
  schema = SchemaBytes emptySchemaInfo emptyBytesSchema

instance HasSchema Bool ts where
  schema = SchemaBuiltInBoolean emptySchemaInfo

instance HasSchema BuiltinString ts where
  schema = SchemaBuiltInString emptySchemaInfo

instance HasSchema BuiltinData ts where
  schema = SchemaBuiltInData emptySchemaInfo

instance (HasSchema a ts, HasSchema b ts) => HasSchema (a, b) ts where
  schema =
    SchemaBuiltInPair
      emptySchemaInfo
      MkPairSchema{left = schema @a @ts, right = schema @b @ts}

instance (HasSchema a ts) => HasSchema [a] ts where
  schema = SchemaBuiltInList emptySchemaInfo (schema @a @ts)
