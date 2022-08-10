-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE DerivingVia     #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module PlutusLedgerApi.V1.Crypto
    ( PubKeyHash(..)
    ) where

import Control.DeepSeq (NFData)
import Data.String
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Bytes (LedgerBytes (..))
import PlutusTx qualified
import PlutusTx.Lift (makeLift)
import PlutusTx.Prelude qualified as PlutusTx
import Prettyprinter

{- | The hash of a public key. This is frequently used to identify the public key,
rather than the key itself. Hashed with `BLAKE2b-224`. 28 bytes.
This is a simple type without any validation, __use with caution__.
You may want to add checks for its invariants. See the
 [Shelly ledger specification](https://hydra.iohk.io/build/16861845/download/1/ledger-spec.pdf).
-}
newtype PubKeyHash = PubKeyHash { getPubKeyHash :: PlutusTx.BuiltinByteString }
    deriving stock (Eq, Ord, Generic)
    deriving anyclass (NFData)
    deriving newtype (PlutusTx.Eq, PlutusTx.Ord, PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)
    deriving
        (IsString        -- ^ from hex encoding
        , Show           -- ^ using hex encoding
        , Pretty         -- ^ using hex encoding
        ) via LedgerBytes
makeLift ''PubKeyHash
