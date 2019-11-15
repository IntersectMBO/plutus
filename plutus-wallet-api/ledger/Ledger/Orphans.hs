{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE TypeApplications   #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Ledger.Orphans where

import           Codec.Serialise.Class      (Serialise, decode, encode)
import           Crypto.Hash                (Digest, SHA256, digestFromByteString)
import           Data.Aeson                 (FromJSON (parseJSON), ToJSON (toJSON))
import qualified Data.Aeson                 as JSON
import qualified Data.Aeson.Extras          as JSON
import qualified Data.ByteArray             as BA
import qualified Data.ByteString            as BSS
import           IOTS                       (IotsType (iotsDefinition))
import           Language.PlutusTx          (Data)
import qualified Language.PlutusTx.AssocMap as Map
import qualified Language.PlutusTx.Prelude  as P
import           Schema                     (FormSchema (FormSchemaHex), ToSchema (toSchema))
import           Type.Reflection            (Typeable)

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

instance ToSchema (Digest SHA256) where
  toSchema = FormSchemaHex

instance ToSchema P.ByteString where
  toSchema = toSchema @String

instance IotsType (Digest SHA256) where
  iotsDefinition = iotsDefinition @String

instance IotsType P.ByteString where
  iotsDefinition = iotsDefinition @String

instance IotsType Data where
  iotsDefinition = iotsDefinition @String

instance (ToSchema k, ToSchema v) => ToSchema (Map.Map k v)

instance (Typeable k, Typeable v, IotsType k, IotsType v) =>
         IotsType (Map.Map k v)
