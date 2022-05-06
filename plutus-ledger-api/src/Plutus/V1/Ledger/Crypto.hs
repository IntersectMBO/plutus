{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module Plutus.V1.Ledger.Crypto(
    PubKeyHash(..),
    pubKeyHash
    ) where

import Control.DeepSeq (NFData)
import Data.ByteString qualified as BS
import Data.String
import GHC.Generics (Generic)
import Plutus.V1.Ledger.Bytes (LedgerBytes (..))
import PlutusTx qualified
import PlutusTx.Lift (makeLift)
import PlutusTx.Prelude qualified as PlutusTx
import Prettyprinter

-- | The hash of a public key. This is frequently used to identify the public key, rather than the key itself.
-- Should be 28 bytes.
newtype PubKeyHash = UnsafePubKeyHash { getPubKeyHash :: PlutusTx.BuiltinByteString }
    deriving stock (Eq, Ord, Generic)
    deriving anyclass (NFData)
    deriving newtype (PlutusTx.Eq, PlutusTx.Ord, PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)
    deriving
        (IsString        -- ^ from hex encoding
        , Show           -- ^ using hex encoding
        , Pretty         -- ^ using hex encoding
        ) via LedgerBytes
makeLift ''PubKeyHash

pubKeyHash :: BS.ByteString -> Maybe PubKeyHash
pubKeyHash bs =
    if BS.length bs /= 28 then
        Nothing
    else
        Just $ UnsafePubKeyHash $ PlutusTx.toBuiltin bs
