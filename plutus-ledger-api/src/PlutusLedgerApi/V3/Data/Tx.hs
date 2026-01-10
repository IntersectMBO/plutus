{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}

module PlutusLedgerApi.V3.Data.Tx
  ( TxId (..)
  , TxOutRef
  , pattern TxOutRef
  , txOutRefId
  , txOutRefIdx
  ) where

import Control.DeepSeq (NFData)
import Data.Function ((&))
import Data.String (IsString)
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Bytes (LedgerBytes (..))
import PlutusTx qualified
import PlutusTx.AsData qualified as PlutusTx
import PlutusTx.Blueprint.Class (HasBlueprintSchema (..))
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition)
import PlutusTx.Blueprint.Schema (withSchemaInfo)
import PlutusTx.Blueprint.Schema.Annotation (SchemaInfo (..))
import PlutusTx.Builtins.Internal qualified as PlutusTx
import PlutusTx.Eq qualified as PlutusTx
import PlutusTx.IsData.Class (FromData, ToData, UnsafeFromData)
import PlutusTx.Lift (makeLift)
import PlutusTx.Ord qualified as PlutusTx
import Prettyprinter (Pretty, pretty)

{-| A transaction ID, i.e. the hash of a transaction. Hashed with BLAKE2b-256. 32 byte.

This is a simple type without any validation, __use with caution__.
You may want to add checks for its invariants. See the Shelley ledger specification. -}
newtype TxId = TxId {getTxId :: PlutusTx.BuiltinByteString}
  deriving stock (Eq, Ord, Generic)
  deriving anyclass (NFData, HasBlueprintDefinition)
  deriving newtype (PlutusTx.Eq, PlutusTx.Ord, ToData, FromData, UnsafeFromData)
  deriving
    ( IsString
      -- ^ from hex encoding
    , Show
      -- ^ using hex encoding
    , Pretty
      -- ^ using hex encoding
    )
    via LedgerBytes

instance HasBlueprintSchema TxId referencedTypes where
  schema =
    schema @PlutusTx.BuiltinByteString
      & withSchemaInfo \info ->
        info {title = Just "TxId"}

{-| A reference to a transaction output. This is a
pair of a transaction ID (`TxId`), and an index indicating which of the outputs
of that transaction we are referring to. -}
PlutusTx.asData
  [d|
    data TxOutRef = TxOutRef
      { txOutRefId :: TxId
      , -- \^ The transaction ID.
        txOutRefIdx :: Integer
      }
      -- \^ Index into the referenced transaction's outputs

      deriving stock (Show, Eq, Ord, Generic)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
      deriving anyclass (NFData, HasBlueprintDefinition)
    |]

PlutusTx.deriveEq ''TxOutRef

instance Pretty TxOutRef where
  pretty TxOutRef {txOutRefId = id', txOutRefIdx = idx} = pretty id' <> "!" <> pretty idx

----------------------------------------------------------------------------------------------------
-- TH Splices --------------------------------------------------------------------------------------

$(makeLift ''TxId)
$(makeLift ''TxOutRef)
