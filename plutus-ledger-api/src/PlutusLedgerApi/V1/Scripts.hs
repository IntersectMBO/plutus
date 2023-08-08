-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

-- | Functions for working with scripts on the ledger.
module PlutusLedgerApi.V1.Scripts
    (
    ScriptError (..)
    , Redeemer(..)
    , Datum(..)
    , Context(..)
    , DatumHash(..)
    , RedeemerHash(..)
    , ScriptHash(..)
    ) where

import Prelude qualified as Haskell

import Codec.Serialise (Serialise (..))
import Control.DeepSeq (NFData)
import Data.String
import Data.Text (Text)
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Bytes (LedgerBytes (..))
import PlutusTx (FromData (..), ToData (..), UnsafeFromData (..), makeLift)
import PlutusTx.Builtins as Builtins
import PlutusTx.Builtins.Internal as BI
import PlutusTx.Prelude
import Prettyprinter

{- Note [Serialise instances for Datum and Redeemer]
The `Serialise` instances for `Datum` and `Redeemer` exist for several reasons:

- They are useful for the indexers in plutus-apps
- There's clearly only one sensible way to encode `Datum` and `Redeemer` into CBOR,
  since they just wrap `PLC.Data`.
- The encoders and decoders are annoying to implement downstream, because one would
  have to import `BuiltinData` which is from a different package.
-}

-- | A higher-level evaluation error.
-- FIXME: move to /plutus-apps/.
data ScriptError =
    EvaluationError ![Text] !Haskell.String -- ^ Expected behavior of the engine (e.g. user-provided error)
    | EvaluationException !Haskell.String !Haskell.String -- ^ Unexpected behavior of the engine (a bug)
    deriving stock (Haskell.Show, Haskell.Eq, Generic)
    deriving anyclass (NFData)

-- | 'Datum' is a wrapper around 'Data' values which are used as data in transaction outputs.
newtype Datum = Datum { getDatum :: BuiltinData  }
  deriving stock (Generic, Haskell.Show)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, ToData, FromData, UnsafeFromData, Pretty)
  deriving anyclass (NFData)

-- See Note [Serialise instances for Datum and Redeemer]
instance Serialise Datum where
    encode (Datum (BuiltinData d)) = encode d
    decode = Datum . BuiltinData Haskell.<$> decode

-- | 'Redeemer' is a wrapper around 'Data' values that are used as redeemers in transaction inputs.
newtype Redeemer = Redeemer { getRedeemer :: BuiltinData }
  deriving stock (Generic, Haskell.Show)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, ToData, FromData, UnsafeFromData, Pretty)
  deriving anyclass (NFData)

-- See Note [Serialise instances for Datum and Redeemer]
instance Serialise Redeemer where
    encode (Redeemer (BuiltinData d)) = encode d
    decode = Redeemer . BuiltinData Haskell.<$> decode

-- | Script runtime representation of a @Digest SHA256@.
newtype ScriptHash =
    ScriptHash { getScriptHash :: Builtins.BuiltinByteString }
    deriving
        (IsString        -- ^ from hex encoding
        , Haskell.Show   -- ^ using hex encoding
        , Pretty         -- ^ using hex encoding
        ) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, ToData, FromData, UnsafeFromData)
    deriving anyclass (NFData)

-- | Script runtime representation of a @Digest SHA256@.
newtype DatumHash =
    DatumHash Builtins.BuiltinByteString
    deriving
        (IsString        -- ^ from hex encoding
        , Haskell.Show   -- ^ using hex encoding
        , Pretty         -- ^ using hex encoding
        ) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, ToData, FromData, UnsafeFromData)
    deriving anyclass (NFData)

{- | Type representing the /BLAKE2b-256/ hash of a redeemer. 32 bytes.

This is a simple type without any validation, __use with caution__.
You may want to add checks for its invariants. See the
 [Shelley ledger specification](https://hydra.iohk.io/build/16861845/download/1/ledger-spec.pdf).
-}
newtype RedeemerHash =
    RedeemerHash Builtins.BuiltinByteString
    deriving
        (IsString        -- ^ from hex encoding
        , Haskell.Show   -- ^ using hex encoding
        , Pretty         -- ^ using hex encoding
        ) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, ToData, FromData, UnsafeFromData)
    deriving anyclass (NFData)

-- | Information about the state of the blockchain and about the transaction
--   that is currently being validated, represented as a value in 'Data'.
newtype Context = Context BuiltinData
    deriving newtype (Pretty, Haskell.Show)

makeLift ''ScriptHash

makeLift ''DatumHash

makeLift ''RedeemerHash

makeLift ''Datum

makeLift ''Redeemer
