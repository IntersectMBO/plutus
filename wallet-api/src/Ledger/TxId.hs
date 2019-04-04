{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}

-- ToJSON/FromJSON/Serialise (Digest SHA256)
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | The type of transaction IDs
module Ledger.TxId(
    TxIdOf(..)
    , TxId
    ) where

import           Codec.Serialise.Class        (Serialise, decode, encode)
import           Crypto.Hash                  (Digest, SHA256, digestFromByteString)
import           Data.Aeson                   (FromJSON (parseJSON), ToJSON (toJSON))
import qualified Data.Aeson                   as JSON
import qualified Data.Aeson.Extras            as JSON
import qualified Data.ByteArray               as BA
import qualified Data.ByteString              as BSS
import           Data.Proxy                   (Proxy (Proxy))
import           Data.Swagger.Internal.Schema (ToSchema (declareNamedSchema), paramSchemaToSchema, plain)
import           GHC.Generics                 (Generic)
import           Language.PlutusTx.Lift       (makeLift)

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

instance ToSchema (Digest SHA256) where
    declareNamedSchema _ = plain $ paramSchemaToSchema (Proxy @String)

instance FromJSON (Digest SHA256) where
    parseJSON = JSON.decodeSerialise

-- | A transaction ID, using some id type.
newtype TxIdOf h = TxIdOf { getTxId :: h }
    deriving (Eq, Ord, Show)
    deriving stock (Generic)

makeLift ''TxIdOf

-- | A transaction id, using a SHA256 hash as the transaction id type.
type TxId = TxIdOf (Digest SHA256)

deriving newtype instance Serialise TxId
deriving anyclass instance ToJSON a => ToJSON (TxIdOf a)
deriving anyclass instance FromJSON a => FromJSON (TxIdOf a)
deriving anyclass instance ToSchema a => ToSchema (TxIdOf a)
