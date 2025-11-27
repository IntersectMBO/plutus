-- editorconfig-checker-disable-file
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Functions for working with scripts on the ledger.
module PlutusLedgerApi.V1.Scripts
  ( ScriptError (..)
  , Redeemer (..)
  , Datum (..)
  , Context (..)
  , DatumHash (..)
  , RedeemerHash (..)
  , ScriptHash (..)
  ) where

import PlutusTx.Prelude
import Prelude qualified as Haskell

import Codec.Serialise (Serialise (..))
import Control.DeepSeq (NFData)
import Data.String (IsString)
import Data.Text (Text)
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Bytes (LedgerBytes (..))
import PlutusTx (makeLift)
import PlutusTx.Blueprint.Class (HasBlueprintSchema (..))
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition (..))
import PlutusTx.Blueprint.Schema (Schema (..), emptyBytesSchema)
import PlutusTx.Blueprint.Schema.Annotation (SchemaInfo (..), emptySchemaInfo)
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Builtins.Internal as BI
import PlutusTx.Show (deriveShow)
import Prettyprinter (Pretty)

{- Note [Serialise instances for Datum and Redeemer]
The `Serialise` instances for `Datum` and `Redeemer` exist for several reasons:

- They are useful for the indexers in plutus-apps
- There's clearly only one sensible way to encode `Datum` and `Redeemer` into CBOR,
  since they just wrap `PLC.Data`.
- The encoders and decoders are annoying to implement downstream, because one would
  have to import `BuiltinData` which is from a different package.
-}

-- | A higher-level evaluation error.
data ScriptError
  = -- | Expected behavior of the engine (e.g. user-provided error)
    EvaluationError ![Text] !Haskell.String
  | -- | Unexpected behavior of the engine (a bug)
    EvaluationException !Haskell.String !Haskell.String
  deriving stock (Haskell.Show, Haskell.Eq, Generic)
  deriving anyclass (NFData, HasBlueprintDefinition)

-- | 'Datum' is a wrapper around 'Data' values which are used as data in transaction outputs.
newtype Datum = Datum {getDatum :: BuiltinData}
  deriving stock (Generic, Haskell.Show)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, ToData, FromData, UnsafeFromData, Pretty)
  deriving anyclass (NFData, HasBlueprintDefinition)

instance HasBlueprintSchema Datum referencedTypes where
  schema = SchemaBuiltInData emptySchemaInfo {title = Just "Datum"}

-- See Note [Serialise instances for Datum and Redeemer]
instance Serialise Datum where
  encode (Datum (BuiltinData d)) = encode d
  decode = Datum . BuiltinData Haskell.<$> decode

-- | 'Redeemer' is a wrapper around 'Data' values that are used as redeemers in transaction inputs.
newtype Redeemer = Redeemer {getRedeemer :: BuiltinData}
  deriving stock (Generic, Haskell.Show)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, ToData, FromData, UnsafeFromData, Pretty)
  deriving anyclass (NFData, HasBlueprintDefinition)

instance HasBlueprintSchema Redeemer referencedTypes where
  schema = SchemaBuiltInData emptySchemaInfo {title = Just "Redeemer"}

-- See Note [Serialise instances for Datum and Redeemer]
instance Serialise Redeemer where
  encode (Redeemer (BuiltinData d)) = encode d
  decode = Redeemer . BuiltinData Haskell.<$> decode

{-| Type representing the /BLAKE2b-224/ hash of a script. 28 bytes.

This is a simple type without any validation, __use with caution__.
You may want to add checks for its invariants.
See the [Shelley ledger specification](https://github.com/IntersectMBO/cardano-ledger/releases/download/cardano-ledger-spec-2023-04-03/shelley-ledger.pdf). -}
newtype ScriptHash = ScriptHash {getScriptHash :: Builtins.BuiltinByteString}
  deriving
    ( IsString
      -- ^ from hex encoding
    , Haskell.Show
      -- ^ using hex encoding
    , Pretty
      -- ^ using hex encoding
    )
    via LedgerBytes
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, ToData, FromData, UnsafeFromData)
  deriving anyclass (NFData, HasBlueprintDefinition)

instance HasBlueprintSchema ScriptHash referencedTypes where
  schema = SchemaBytes emptySchemaInfo {title = Just "ScriptHash"} emptyBytesSchema

{-| Type representing the /BLAKE2b-256/ hash of a datum. 32 bytes.

This is a simple type without any validation, __use with caution__.
You may want to add checks for its invariants.
See the [Shelley ledger specification](https://github.com/IntersectMBO/cardano-ledger/releases/download/cardano-ledger-spec-2023-04-03/shelley-ledger.pdf). -}
newtype DatumHash = DatumHash Builtins.BuiltinByteString
  deriving
    ( IsString
      -- ^ from hex encoding
    , Haskell.Show
      -- ^ using hex encoding
    , Pretty
      -- ^ using hex encoding
    )
    via LedgerBytes
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, ToData, FromData, UnsafeFromData)
  deriving anyclass (NFData, HasBlueprintDefinition)

instance HasBlueprintSchema DatumHash referencedTypes where
  schema = SchemaBytes emptySchemaInfo {title = Just "DatumHash"} emptyBytesSchema

{-| Type representing the /BLAKE2b-256/ hash of a redeemer. 32 bytes.

This is a simple type without any validation, __use with caution__.
You may want to add checks for its invariants.
See the [Shelley ledger specification](https://github.com/IntersectMBO/cardano-ledger/releases/download/cardano-ledger-spec-2023-04-03/shelley-ledger.pdf). -}
newtype RedeemerHash = RedeemerHash Builtins.BuiltinByteString
  deriving
    ( IsString
      -- ^ from hex encoding
    , Haskell.Show
      -- ^ using hex encoding
    , Pretty
      -- ^ using hex encoding
    )
    via LedgerBytes
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, ToData, FromData, UnsafeFromData)
  deriving anyclass (NFData, HasBlueprintDefinition)

instance HasBlueprintSchema RedeemerHash referencedTypes where
  schema = SchemaBytes emptySchemaInfo {title = Just "RedeemerHash"} emptyBytesSchema

{-| Information about the state of the blockchain and about the transaction
  that is currently being validated, represented as a value in 'Data'. -}
newtype Context = Context BuiltinData
  deriving newtype (Pretty, Haskell.Show)

----------------------------------------------------------------------------------------------------
-- TH Splices --------------------------------------------------------------------------------------

makeLift ''ScriptHash
makeLift ''DatumHash
makeLift ''RedeemerHash
makeLift ''Datum
makeLift ''Redeemer

deriveShow ''ScriptHash
deriveShow ''DatumHash
deriveShow ''RedeemerHash
deriveShow ''Datum
deriveShow ''Redeemer
