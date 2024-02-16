{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module PlutusTx.Blueprint.Class where

import Prelude

import PlutusTx.Blueprint.Schema (DataSchema, dsBuiltInBoolean, dsBuiltInBytes, dsBuiltInData,
                                  dsBuiltInList, dsBuiltInPair, dsBuiltInString, dsBuiltInUnit,
                                  dsInteger)
import PlutusTx.Builtins.Internal (BuiltinBool, BuiltinByteString, BuiltinData, BuiltinList,
                                   BuiltinPair, BuiltinString, BuiltinUnit)

class HasDataSchema a where
  dataSchema :: DataSchema

instance HasDataSchema () where
  dataSchema = dsBuiltInUnit

instance HasDataSchema Integer where
  dataSchema = dsInteger

instance HasDataSchema BuiltinByteString where
  dataSchema = dsBuiltInBytes

instance HasDataSchema BuiltinUnit where
  dataSchema = dsBuiltInUnit

instance HasDataSchema BuiltinBool where
  dataSchema = dsBuiltInBoolean

instance HasDataSchema BuiltinString where
  dataSchema = dsBuiltInString

instance HasDataSchema BuiltinData where
  dataSchema = dsBuiltInData

instance (HasDataSchema a, HasDataSchema b) => HasDataSchema (BuiltinPair a b) where
  dataSchema = dsBuiltInPair (dataSchema @a) (dataSchema @b)

instance (HasDataSchema a) => HasDataSchema (BuiltinList a) where
  dataSchema = dsBuiltInList (dataSchema @a)
