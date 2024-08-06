{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}

module PlutusLedgerApi.V3.Tx (
  TxId (..),
  TxOutRef (..),
) where

import Control.DeepSeq (NFData)
import Data.String (IsString)
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Bytes (LedgerBytes (..))
import PlutusTx qualified
import PlutusTx.Bool qualified as PlutusTx
import PlutusTx.Builtins.Internal qualified as PlutusTx
import PlutusTx.Eq qualified as PlutusTx
import PlutusTx.IsData.Class (FromData, ToData, UnsafeFromData)
import PlutusTx.Ord qualified as PlutusTx
import Prettyprinter (Pretty, pretty)

{- | A transaction ID, i.e. the hash of a transaction. Hashed with BLAKE2b-256. 32 byte.

This is a simple type without any validation, __use with caution__.
You may want to add checks for its invariants. See the Shelley ledger specification.
-}
newtype TxId = TxId {getTxId :: PlutusTx.BuiltinByteString}
  deriving stock (Eq, Ord, Generic)
  deriving anyclass (NFData)
  deriving newtype (PlutusTx.Eq, PlutusTx.Ord, ToData, FromData, UnsafeFromData)
  deriving
    ( -- | from hex encoding
      IsString
    , -- | using hex encoding
      Show
    , -- | using hex encoding
      Pretty
    )
    via LedgerBytes

{- | A reference to a transaction output. This is a
pair of a transaction ID (`TxId`), and an index indicating which of the outputs
of that transaction we are referring to.
-}
data TxOutRef = TxOutRef
  { txOutRefId  :: TxId
  -- ^ The transaction ID.
  , txOutRefIdx :: Integer
  -- ^ Index into the referenced transaction's outputs
  }
  deriving stock (Show, Eq, Ord, Generic)
  deriving anyclass (NFData)

instance Pretty TxOutRef where
  pretty TxOutRef{txOutRefId, txOutRefIdx} = pretty txOutRefId <> "!" <> pretty txOutRefIdx

instance PlutusTx.Eq TxOutRef where
  {-# INLINEABLE (==) #-}
  l == r =
    (txOutRefId l PlutusTx.== txOutRefId r)
      PlutusTx.&& (txOutRefIdx l PlutusTx.== txOutRefIdx r)

PlutusTx.makeLift ''TxId

PlutusTx.makeLift ''TxOutRef
PlutusTx.makeIsDataIndexed ''TxOutRef [('TxOutRef, 0)]
