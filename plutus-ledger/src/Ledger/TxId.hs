{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -fno-strictness   #-}

-- | The type of transaction IDs
module Ledger.TxId(
    TxId (..)
    ) where

import           Codec.Serialise.Class     (Serialise)
import           Control.DeepSeq           (NFData)
import           Data.Aeson                (FromJSON, FromJSONKey, ToJSON, ToJSONKey)
import qualified Data.ByteString           as BS
import           Data.Text.Prettyprint.Doc (Pretty)
import           GHC.Generics              (Generic)
import           IOTS                      (IotsType)
import qualified Language.PlutusTx         as PlutusTx
import qualified Language.PlutusTx.Prelude as PlutusTx
import           Ledger.Orphans            ()
import           LedgerBytes               (LedgerBytes (..))

-- | A transaction ID, using a SHA256 hash as the transaction id.
newtype TxId = TxId { getTxId :: BS.ByteString }
    deriving (Eq, Ord, Generic)
    deriving anyclass (ToJSON, ToJSONKey, FromJSON, FromJSONKey, IotsType, NFData)
    deriving newtype (PlutusTx.Eq, PlutusTx.Ord, Serialise)
    deriving (Show, Pretty) via LedgerBytes

PlutusTx.makeLift ''TxId
PlutusTx.makeIsData ''TxId
