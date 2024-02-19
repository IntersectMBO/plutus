{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}

module PlutusTx.Blueprint.Class where

import Prelude

import Data.Kind (Type)
import PlutusTx.Blueprint.Schema (Schema (..))
import PlutusTx.Builtins (BuiltinByteString, BuiltinData, BuiltinString)

class HasDataSchema (t :: Type) (canReferTypes :: [Type]) where
  dataSchema :: Schema

instance HasDataSchema () ts where
  dataSchema =
    SchemaBuiltInUnit
      Nothing -- Title
      Nothing -- Description
      Nothing -- Comment

instance HasDataSchema Integer ts where
  dataSchema =
    SchemaInteger
      Nothing -- Title
      Nothing -- Description
      Nothing -- Comment
      Nothing -- Multiple of
      Nothing -- Maximum
      Nothing -- Exclusive maximum
      Nothing -- Minimum
      Nothing -- Exclusive minimum

instance HasDataSchema BuiltinByteString ts where
  dataSchema =
    SchemaBytes
      Nothing -- Title
      Nothing -- Description
      Nothing -- Comment
      [] -- Enum
      Nothing -- Min length
      Nothing -- Max length

instance HasDataSchema Bool ts where
  dataSchema =
    SchemaBuiltInBoolean
      Nothing -- Title
      Nothing -- Description
      Nothing -- Comment

instance HasDataSchema BuiltinString ts where
  dataSchema =
    SchemaBuiltInString
      Nothing -- Title
      Nothing -- Description
      Nothing -- Comment

instance HasDataSchema BuiltinData ts where
  dataSchema =
    SchemaBuiltInData
      Nothing -- Title
      Nothing -- Description
      Nothing -- Comment

instance (HasDataSchema a ts, HasDataSchema b ts) => HasDataSchema (a, b) ts where
  dataSchema =
    SchemaBuiltInPair
      Nothing -- Title
      Nothing -- Description
      Nothing -- Comment
      (dataSchema @a @ts)
      (dataSchema @b @ts)

instance (HasDataSchema a ts) => HasDataSchema [a] ts where
  dataSchema =
    SchemaBuiltInList
      Nothing -- Title
      Nothing -- Description
      Nothing -- Comment
      (dataSchema @a @ts)
