{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

-- | The type of transaction IDs
module Plutus.V1.Ledger.TxId(
    TxId (..)
    ) where

import Codec.Serialise.Class (Serialise)
import Control.DeepSeq (NFData)
import Data.Aeson (FromJSON, FromJSONKey, ToJSON, ToJSONKey)
import Data.String (IsString)
import GHC.Generics (Generic)
import Plutus.V1.Ledger.Bytes (LedgerBytes (..))
import Plutus.V1.Ledger.Orphans ()
import PlutusTx qualified as PlutusTx
import PlutusTx.Prelude qualified as PlutusTx
import Prettyprinter (Pretty)

-- | A transaction ID, using a SHA256 hash as the transaction id.
newtype TxId = TxId { getTxId :: PlutusTx.BuiltinByteString }
    deriving (Eq, Ord, Generic)
    deriving anyclass (ToJSON, FromJSON, ToJSONKey, FromJSONKey, NFData)
    deriving newtype (PlutusTx.Eq, PlutusTx.Ord, Serialise)
    deriving (Show, Pretty, IsString) via LedgerBytes

PlutusTx.makeLift ''TxId
PlutusTx.makeIsDataIndexed ''TxId [('TxId,0)]
