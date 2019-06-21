{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}

-- ToJSON/FromJSON/Serialise (Digest SHA256)
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | The type of transaction IDs
module Ledger.TxId(
    TxIdOf(..)
    , TxId
    ) where

import           Codec.Serialise.Class  (Serialise, decode, encode)
import           Crypto.Hash            (Digest, SHA256, digestFromByteString)
import           Data.Aeson             (FromJSON (parseJSON), ToJSON (toJSON))
import qualified Data.Aeson             as JSON
import qualified Data.Aeson.Extras      as JSON
import qualified Data.ByteArray         as BA
import qualified Data.ByteString        as BSS
import           Data.Morpheus.Kind     (KIND, OBJECT, SCALAR)
import           Data.Morpheus.Types    (GQLScalar, GQLType, parseValue, serialize, typeID)
import qualified Data.Morpheus.Types    as Morpheus
import qualified Data.Text              as Text
import qualified Data.Text.Encoding     as Text
import           GHC.Generics           (Generic)
import           Language.PlutusTx.Lift (makeLift)

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

-- | A transaction ID, using some id type.
newtype TxIdOf h = TxIdOf { getTxId :: h }
    deriving (Eq, Ord, Show, Generic)
    deriving anyclass (GQLType)

type instance KIND (TxIdOf h) = OBJECT

makeLift ''TxIdOf

type instance KIND (Digest SHA256) = SCALAR

instance GQLType (Digest SHA256) where
  typeID _ = "DigestSHA256"

instance GQLScalar (Digest SHA256) where
  parseValue (Morpheus.String raw) =
    case digestFromByteString . Text.encodeUtf8 $ raw of
        Nothing ->  Left $ "Expected DigestSHA256 string, got: " <> Text.pack (show raw)
        Just v  -> Right v
  parseValue other =
        Left $ "Expected DigestSHA256 string, got: " <> Text.pack (show other)
  serialize = Morpheus.String . JSON.encodeSerialise

-- | A transaction id, using a SHA256 hash as the transaction id type.
type TxId = TxIdOf (Digest SHA256)

deriving newtype instance Serialise TxId
deriving anyclass instance ToJSON a => ToJSON (TxIdOf a)
deriving anyclass instance FromJSON a => FromJSON (TxIdOf a)
