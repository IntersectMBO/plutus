{-# LANGUAGE DataKinds #-}
-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module PlutusLedgerApi.V1.Crypto
  ( PubKeyHash (..)
  ) where

import Control.DeepSeq (NFData)
import Data.String
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Bytes (LedgerBytes (..))
import PlutusTx qualified
import PlutusTx.Blueprint.Class (HasBlueprintSchema (..))
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition (Unroll))
import PlutusTx.Blueprint.Schema (Schema (..), emptyBytesSchema)
import PlutusTx.Blueprint.Schema.Annotation (SchemaInfo (..), emptySchemaInfo)
import PlutusTx.Lift (makeLift)
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Show qualified as PlutusTx
import Prettyprinter

{-| The hash of a public key. This is frequently used to identify the public key,
rather than the key itself. Hashed with /BLAKE2b-224/. 28 bytes.

This is a simple type without any validation, __use with caution__.
You may want to add checks for its invariants. See the
 [Shelley ledger specification](https://github.com/IntersectMBO/cardano-ledger/releases/download/cardano-ledger-spec-2023-04-03/shelley-ledger.pdf). -}
newtype PubKeyHash = PubKeyHash {getPubKeyHash :: PlutusTx.BuiltinByteString}
  deriving stock (Eq, Ord, Generic)
  deriving anyclass (NFData)
  deriving newtype
    ( PlutusTx.Eq
    , PlutusTx.Ord
    , PlutusTx.Show
    , PlutusTx.ToData
    , PlutusTx.FromData
    , PlutusTx.UnsafeFromData
    )
  deriving
    ( IsString
      -- ^ from hex encoding
    , Show
      -- ^ using hex encoding
    , Pretty
      -- ^ using hex encoding
    )
    via LedgerBytes

instance HasBlueprintSchema PubKeyHash referenedTypes where
  {-# INLINEABLE schema #-}
  schema = SchemaBytes emptySchemaInfo {title = Just "PubKeyHash"} emptyBytesSchema

instance HasBlueprintDefinition PubKeyHash where
  type Unroll PubKeyHash = '[PubKeyHash]

----------------------------------------------------------------------------------------------------
-- TH Splices --------------------------------------------------------------------------------------

$(makeLift ''PubKeyHash)
