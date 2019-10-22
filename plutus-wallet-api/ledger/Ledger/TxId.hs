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
import qualified Data.Aeson.Extras         as JSON
import qualified Data.ByteString.Lazy      as BSL
import           Data.Text.Prettyprint.Doc (Pretty (pretty), (<+>))
import           GHC.Generics              (Generic)
import           IOTS                      (IotsType)
import qualified Language.PlutusTx         as PlutusTx
import qualified Language.PlutusTx.Prelude as PlutusTx
import           Ledger.Orphans            ()
import           LedgerBytes               (LedgerBytes (..))
import           Schema                    (ToSchema)

-- | A transaction ID, using a SHA256 hash as the transaction id.
newtype TxId = TxId { getTxId :: BSL.ByteString }
    deriving (Eq, Ord, Show, Generic)
    deriving anyclass (ToSchema)
    deriving newtype (PlutusTx.Eq, PlutusTx.Ord)

deriving newtype instance Serialise TxId
deriving via LedgerBytes instance ToJSON TxId
deriving via LedgerBytes instance FromJSON TxId
deriving anyclass instance IotsType TxId

instance Pretty TxId where
    pretty t = "TxId:" <+> pretty (JSON.encodeSerialise $ getTxId t)

PlutusTx.makeLift ''TxId
PlutusTx.makeIsData ''TxId
