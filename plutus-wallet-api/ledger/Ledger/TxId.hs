{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE OverloadedStrings  #-}
-- ToJSON/FromJSON/Serialise (Digest SHA256)
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | The type of transaction IDs
module Ledger.TxId(
    TxId (..)
    ) where

import           Codec.Serialise.Class     (Serialise, decode, encode)
import           Crypto.Hash               (Digest, SHA256, digestFromByteString)
import           Data.Aeson                (FromJSON (parseJSON), ToJSON (toJSON))
import qualified Data.Aeson                as JSON
import qualified Data.Aeson.Extras         as JSON
import qualified Data.ByteArray            as BA
import qualified Data.ByteString           as BSS
import           Data.Text.Prettyprint.Doc (Pretty (pretty), (<+>))
import           GHC.Generics              (Generic)
import           Ledger.Orphans            ()
import           Schema                    (ToSchema)

instance Serialise (Digest SHA256) where
    encode = encode . BA.unpack
    decode = do
      d <- decode
      let md = digestFromByteString . BSS.pack $ d
      case md of
        Nothing -> fail "couldn't decode to Digest SHA256"
        Just v  -> pure v

instance ToJSON (Digest SHA256) where
    toJSON = JSON.String . JSON.encodeSerialise

instance FromJSON (Digest SHA256) where
    parseJSON = JSON.decodeSerialise

-- | A transaction ID, using a SHA256 hash as the transaction id.
newtype TxId = TxId { getTxId :: Digest SHA256 }
    deriving (Eq, Ord, Show, Generic)
    deriving anyclass (ToSchema)

deriving newtype instance Serialise TxId
deriving anyclass instance ToJSON TxId
deriving anyclass instance FromJSON TxId

instance Pretty TxId where
    pretty t = "TxId:" <+> pretty (JSON.encodeSerialise $ getTxId t)
