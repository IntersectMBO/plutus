{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module PlutusLedgerApi.V4.Internal (ListEncoded (..)) where

import PlutusTx.Blueprint.Class (HasBlueprintSchema (..))
import PlutusTx.Blueprint.Schema (ConstructorSchema (..), Schema (..))
import PlutusTx.Builtins qualified as Builtins (matchData')
import PlutusTx.Builtins.Internal qualified as Builtins
import PlutusTx.IsData.Class (FromData (..), ToData (..), UnsafeFromData (..))
import PlutusTx.Prelude qualified as PlutusTx

newtype ListEncoded wrapped = ListEncoded wrapped

instance ToData wrapped => ToData (ListEncoded wrapped) where
  {-# INLINEABLE toBuiltinData #-}
  toBuiltinData (ListEncoded value) =
    Builtins.mkList (Builtins.snd (Builtins.unsafeDataAsConstr (toBuiltinData value)))

instance FromData wrapped => FromData (ListEncoded wrapped) where
  {-# INLINEABLE fromBuiltinData #-}
  fromBuiltinData value =
    Builtins.matchData'
      value
      (\_ _ -> Nothing)
      (\_ -> Nothing)
      (\fields -> ListEncoded PlutusTx.<$> fromBuiltinData (Builtins.mkConstr 0 fields))
      (\_ -> Nothing)
      (\_ -> Nothing)

instance UnsafeFromData wrapped => UnsafeFromData (ListEncoded wrapped) where
  {-# INLINEABLE unsafeFromBuiltinData #-}
  unsafeFromBuiltinData value =
    ListEncoded (unsafeFromBuiltinData (Builtins.mkConstr 0 (Builtins.unsafeDataAsList value)))

instance
  HasBlueprintSchema wrapped referencedTypes
  => HasBlueprintSchema (ListEncoded wrapped) referencedTypes
  where
  schema = case schema @wrapped @referencedTypes of
    SchemaConstructor info (MkConstructorSchema 0 fields) -> SchemaListTuple info fields
    _ -> error "ListEncoded requires a product schema with constructor index zero"
