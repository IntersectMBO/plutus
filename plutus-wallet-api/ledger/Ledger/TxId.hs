{-# LANGUAGE DataKinds         #-}
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
import           Data.Aeson                (FromJSON, ToJSON)
import qualified Data.ByteString.Lazy      as BSL
import           Data.Text.Prettyprint.Doc (Pretty)
import           Data.Text.Prettyprint.Doc.Extras
import           GHC.Generics              (Generic)
import           IOTS                      (IotsType)
import qualified Language.PlutusTx         as PlutusTx
import qualified Language.PlutusTx.Prelude as PlutusTx
import           LedgerBytes               (LedgerBytes(..))
import           Ledger.Orphans            ()
import           Schema                    (ToSchema)

-- | A transaction ID, using a SHA256 hash as the transaction id.
newtype TxId = TxId { getTxId :: BSL.ByteString }
    deriving (Eq, Ord, Generic)
    deriving anyclass (ToSchema, IotsType)
    deriving newtype (PlutusTx.Eq, PlutusTx.Ord, Serialise)
    deriving (ToJSON, FromJSON, Show) via LedgerBytes
    deriving Pretty via (Tagged "TxId:" LedgerBytes)

PlutusTx.makeLift ''TxId
PlutusTx.makeIsData ''TxId
